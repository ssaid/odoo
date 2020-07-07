# -*- coding: utf-8 -*-
import commands
import logging
_logger = logging.getLogger(__name__)
import simplejson
import os
import os.path
import io
import base64
import openerp
import time
import random
import math
import md5
import openerp.addons.hw_proxy.controllers.main as hw_proxy
import pickle
import re
import subprocess
import traceback
from lxml import etree as ET

try:
    # from .. escpos import *
    # from .. escpos.exceptions import *
    # from .. escpos.printer import Usb
    # from .. escpos.printer import TmpFile
    import escpos
    from escpos.exceptions import *
    from escpos.printer import Usb
    from escpos.escpos import Escpos
    from escpos.constants import *
except ImportError:
    _logger.exception('Unable to use escpos')
    escpos = printer = None

from threading import Thread, Lock
from Queue import Queue, Empty

try:
    import usb.core
except ImportError:
    usb = None

from PIL import Image

from openerp import http
from openerp.http import request
from openerp.tools.translate import _


# workaround https://bugs.launchpad.net/openobject-server/+bug/947231
# related to http://bugs.python.org/issue7980
from datetime import datetime
datetime.strptime('2012-01-01', '%Y-%m-%d')

# Patch things needed to print in escpos
def utfstr(stuff):
    """ converts stuff to string and does without failing if stuff is a utf8 string """
    if isinstance(stuff,basestring):
        return stuff
    else:
        return str(stuff)


class StyleStack:
    """
    The stylestack is used by the xml receipt serializer to compute the active styles along the xml
    document. Styles are just xml attributes, there is no css mechanism. But the style applied by
    the attributes are inherited by deeper nodes.
    """
    def __init__(self):
        self.stack = []
        self.defaults = {   # default style values
            'align':     'left',
            'underline': 'off',
            'bold':      'off',
            'size':      'normal',
            'font'  :    'a',
            'width':     48,
            'indent':    0,
            'tabwidth':  2,
            'bullet':    ' - ',
            'line-ratio':0.5,
            'color':    'black',

            'value-decimals':           2,
            'value-symbol':             '',
            'value-symbol-position':    'after',
            'value-autoint':            'off',
            'value-decimals-separator':  '.',
            'value-thousands-separator': ',',
            'value-width':               0,

        }

        self.types = { # attribute types, default is string and can be ommitted
            'width':    'int',
            'indent':   'int',
            'tabwidth': 'int',
            'line-ratio':       'float',
            'value-decimals':   'int',
            'value-width':      'int',
        }

        self.cmds = {
            # translation from styles to escpos commands
            # some style do not correspond to escpos command are used by
            # the serializer instead
            'align': {
                'left':     TXT_ALIGN_LT,
                'right':    TXT_ALIGN_RT,
                'center':   TXT_ALIGN_CT,
                '_order':   1,
            },
            'underline': {
                'off':      TXT_UNDERL_OFF,
                'on':       TXT_UNDERL_ON,
                'double':   TXT_UNDERL2_ON,
                # must be issued after 'size' command
                # because ESC ! resets ESC -
                '_order':   10,
            },
            'bold': {
                'off':      TXT_BOLD_OFF,
                'on':       TXT_BOLD_ON,
                # must be issued after 'size' command
                # because ESC ! resets ESC -
                '_order':   10,
            },
            'font': {
                'a':        TXT_FONT_A,
                'b':        TXT_FONT_B,
                # must be issued after 'size' command
                # because ESC ! resets ESC -
                '_order':   10,
            },
            'size': {
                'normal':           TXT_NORMAL,
                'double-height':    TXT_2HEIGHT,
                'double-width':     TXT_2WIDTH,
                'double':           TXT_2WIDTH,
                '_order':   1,
            },
            'color': {
                'black':    TXT_COLOR_BLACK,
                'red':      TXT_COLOR_RED,
                '_order':   1,
            },
        }

        self.push(self.defaults)

    def get(self,style):
        """ what's the value of a style at the current stack level"""
        level = len(self.stack) -1
        while level >= 0:
            if style in self.stack[level]:
                return self.stack[level][style]
            else:
                level = level - 1
        return None

    def enforce_type(self, attr, val):
        """converts a value to the attribute's type"""
        if not attr in self.types:
            return utfstr(val)
        elif self.types[attr] == 'int':
            return int(float(val))
        elif self.types[attr] == 'float':
            return float(val)
        else:
            return utfstr(val)

    def push(self, style={}):
        """push a new level on the stack with a style dictionnary containing style:value pairs"""
        _style = {}
        for attr in style:
            if attr in self.cmds and not style[attr] in self.cmds[attr]:
                print('WARNING: ESC/POS PRINTING: ignoring invalid value: '+utfstr(style[attr])+' for style: '+utfstr(attr))
            else:
                _style[attr] = self.enforce_type(attr, style[attr])
        self.stack.append(_style)

    def set(self, style={}):
        """overrides style values at the current stack level"""
        _style = {}
        for attr in style:
            if attr in self.cmds and not style[attr] in self.cmds[attr]:
                print('WARNING: ESC/POS PRINTING: ignoring invalid value: '+utfstr(style[attr])+' for style: '+utfstr(attr))
            else:
                self.stack[-1][attr] = self.enforce_type(attr, style[attr])

    def pop(self):
        """ pop a style stack level """
        if len(self.stack) > 1 :
            self.stack = self.stack[:-1]

    def to_escpos(self):
        """ converts the current style to an escpos command string """
        cmd = ''
        ordered_cmds = self.cmds.keys()
        ordered_cmds.sort(lambda x,y: cmp(self.cmds[x]['_order'], self.cmds[y]['_order']))
        for style in ordered_cmds:
            cmd += self.cmds[style][self.get(style)]
        return cmd

class XmlSerializer:
    """
    Converts the xml inline / block tree structure to a string,
    keeping track of newlines and spacings.
    The string is outputted asap to the provided escpos driver.
    """
    def __init__(self,escpos):
        self.escpos = escpos
        self.stack = ['block']
        self.dirty = False

    def start_inline(self,stylestack=None):
        """ starts an inline entity with an optional style definition """
        self.stack.append('inline')
        if self.dirty:
            self.escpos._raw(' ')
        if stylestack:
            self.style(stylestack)

    def start_block(self,stylestack=None):
        """ starts a block entity with an optional style definition """
        if self.dirty:
            self.escpos._raw('\n')
            self.dirty = False
        self.stack.append('block')
        if stylestack:
            self.style(stylestack)

    def end_entity(self):
        """ ends the entity definition. (but does not cancel the active style!) """
        if self.stack[-1] == 'block' and self.dirty:
            self.escpos._raw('\n')
            self.dirty = False
        if len(self.stack) > 1:
            self.stack = self.stack[:-1]

    def pre(self,text):
        """ puts a string of text in the entity keeping the whitespace intact """
        if text:
            text = text.encode(errors='replace')
            self.escpos.text(text)
            self.dirty = True

    def text(self,text):
        """ puts text in the entity. Whitespace and newlines are stripped to single spaces. """
        if text:
            text = utfstr(text)
            text = text.strip()
            text = re.sub('\s+',' ',text)
            if text:
                self.dirty = True
                self.escpos.text(text)

    def linebreak(self):
        """ inserts a linebreak in the entity """
        self.dirty = False
        self.escpos._raw('\n')

    def style(self,stylestack):
        """ apply a style to the entity (only applies to content added after the definition) """
        self.raw(stylestack.to_escpos())

    def raw(self,raw):
        """ puts raw text or escpos command in the entity without affecting the state of the serializer """
        self.escpos._raw(raw)

class XmlLineSerializer:
    """
    This is used to convert a xml tree into a single line, with a left and a right part.
    The content is not output to escpos directly, and is intended to be fedback to the
    XmlSerializer as the content of a block entity.
    """
    def __init__(self, indent=0, tabwidth=2, width=48, ratio=0.5):
        self.tabwidth = tabwidth
        self.indent = indent
        self.width  = max(0, width - int(tabwidth*indent))
        self.lwidth = int(self.width*ratio)
        self.rwidth = max(0, self.width - self.lwidth)
        self.clwidth = 0
        self.crwidth = 0
        self.lbuffer  = ''
        self.rbuffer  = ''
        self.left    = True

    def _txt(self,txt):
        if self.left:
            if self.clwidth < self.lwidth:
                txt = txt[:max(0, self.lwidth - self.clwidth)]
                self.lbuffer += txt
                self.clwidth += len(txt)
        else:
            if self.crwidth < self.rwidth:
                txt = txt[:max(0, self.rwidth - self.crwidth)]
                self.rbuffer += txt
                self.crwidth  += len(txt)

    def start_inline(self,stylestack=None):
        if (self.left and self.clwidth) or (not self.left and self.crwidth):
            self._txt(' ')

    def start_block(self,stylestack=None):
        self.start_inline(stylestack)

    def end_entity(self):
        pass

    def pre(self,text):
        if text:
            self._txt(text)
    def text(self,text):
        if text:
            text = utfstr(text)
            text = text.strip()
            text = re.sub('\s+',' ',text)
            if text:
                self._txt(text)

    def linebreak(self):
        pass
    def style(self,stylestack):
        pass
    def raw(self,raw):
        pass

    def start_right(self):
        self.left = False

    def get_line(self):
        return ' ' * self.indent * self.tabwidth + self.lbuffer + ' ' * (self.width - self.clwidth - self.crwidth) + self.rbuffer


class UsbPrinter(Usb):
    def print_base64_image(self,img):
        return False


        id = md5.new(img).digest()

        if id not in self.img_cache:

            img = img[img.find(',')+1:]
            f = io.BytesIO('img')
            f.write(base64.decodestring(img))
            f.seek(0)
            img_rgba = Image.open(f)
            img = Image.new('RGB', img_rgba.size, (255,255,255))
            channels = img_rgba.split()
            if len(channels) > 1:
                # use alpha channel as mask
                img.paste(img_rgba, mask=channels[3])
            else:
                img.paste(img_rgba)


            pix_line, img_size = self._convert_image(img)


            buffer = self._raw_print_image(pix_line, img_size)
            self.img_cache[id] = buffer


        self._raw(self.img_cache[id])

    def receipt(self,xml):
        """
        Prints an xml based receipt definition
        """

        def strclean(string):
            if not string:
                string = ''
            string = string.strip()
            string = re.sub('\s+',' ',string)
            return string

        def format_value(value, decimals=3, width=0, decimals_separator='.', thousands_separator=',', autoint=False, symbol='', position='after'):
            decimals = max(0,int(decimals))
            width    = max(0,int(width))
            value    = float(value)

            if autoint and math.floor(value) == value:
                decimals = 0
            if width == 0:
                width = ''

            if thousands_separator:
                formatstr = "{:"+str(width)+",."+str(decimals)+"f}"
            else:
                formatstr = "{:"+str(width)+"."+str(decimals)+"f}"


            ret = formatstr.format(value)
            ret = ret.replace(',','COMMA')
            ret = ret.replace('.','DOT')
            ret = ret.replace('COMMA',thousands_separator)
            ret = ret.replace('DOT',decimals_separator)

            if symbol:
                if position == 'after':
                    ret = ret + symbol
                else:
                    ret = symbol + ret
            return ret

        def print_elem(stylestack, serializer, elem, indent=0):
            elem_styles = {
                'h1': {'bold': 'on', 'size':'double'},
                'h2': {'size':'double'},
                'h3': {'bold': 'on', 'size':'double-height'},
                'h4': {'size': 'double-height'},
                'h5': {'bold': 'on'},
                'em': {'font': 'b'},
                'b':  {'bold': 'on'},
            }

            stylestack.push()
            if elem.tag in elem_styles:
                stylestack.set(elem_styles[elem.tag])
            stylestack.set(elem.attrib)

            if elem.tag in ('p','div','section','article','receipt','header','footer','li','h1','h2','h3','h4','h5'):
                serializer.start_block(stylestack)
                serializer.text(elem.text)
                for child in elem:
                    print_elem(stylestack,serializer,child)
                    serializer.start_inline(stylestack)
                    serializer.text(child.tail)
                    serializer.end_entity()
                serializer.end_entity()

            elif elem.tag in ('span','em','b','left','right'):
                serializer.start_inline(stylestack)
                serializer.text(elem.text)
                for child in elem:
                    print_elem(stylestack,serializer,child)
                    serializer.start_inline(stylestack)
                    serializer.text(child.tail)
                    serializer.end_entity()
                serializer.end_entity()

            elif elem.tag == 'value':
                serializer.start_inline(stylestack)
                serializer.pre(format_value(
                                              elem.text,
                                              decimals=stylestack.get('value-decimals'),
                                              width=stylestack.get('value-width'),
                                              decimals_separator=stylestack.get('value-decimals-separator'),
                                              thousands_separator=stylestack.get('value-thousands-separator'),
                                              autoint=(stylestack.get('value-autoint') == 'on'),
                                              symbol=stylestack.get('value-symbol'),
                                              position=stylestack.get('value-symbol-position')
                                            ))
                serializer.end_entity()

            elif elem.tag == 'line':
                width = stylestack.get('width')
                if stylestack.get('size') in ('double', 'double-width'):
                    width = width / 2

                lineserializer = XmlLineSerializer(stylestack.get('indent')+indent,stylestack.get('tabwidth'),width,stylestack.get('line-ratio'))
                serializer.start_block(stylestack)
                for child in elem:
                    if child.tag == 'left':
                        print_elem(stylestack,lineserializer,child,indent=indent)
                    elif child.tag == 'right':
                        lineserializer.start_right()
                        print_elem(stylestack,lineserializer,child,indent=indent)
                serializer.pre(lineserializer.get_line())
                serializer.end_entity()

            elif elem.tag == 'ul':
                serializer.start_block(stylestack)
                bullet = stylestack.get('bullet')
                for child in elem:
                    if child.tag == 'li':
                        serializer.style(stylestack)
                        serializer.raw(' ' * indent * stylestack.get('tabwidth') + bullet)
                    print_elem(stylestack,serializer,child,indent=indent+1)
                serializer.end_entity()

            elif elem.tag == 'ol':
                cwidth = len(str(len(elem))) + 2
                i = 1
                serializer.start_block(stylestack)
                for child in elem:
                    if child.tag == 'li':
                        serializer.style(stylestack)
                        serializer.raw(' ' * indent * stylestack.get('tabwidth') + ' ' + (str(i)+')').ljust(cwidth))
                        i = i + 1
                    print_elem(stylestack,serializer,child,indent=indent+1)
                serializer.end_entity()

            elif elem.tag == 'pre':
                serializer.start_block(stylestack)
                serializer.pre(elem.text)
                serializer.end_entity()

            elif elem.tag == 'hr':
                width = stylestack.get('width')
                if stylestack.get('size') in ('double', 'double-width'):
                    width = width / 2
                serializer.start_block(stylestack)
                serializer.text('-'*width)
                serializer.end_entity()

            elif elem.tag == 'br':
                serializer.linebreak()

            elif elem.tag == 'img':
                if 'src' in elem.attrib and 'data:' in elem.attrib['src']:
                    self.print_base64_image(elem.attrib['src'])

            elif elem.tag == 'barcode' and 'encoding' in elem.attrib:
                serializer.start_block(stylestack)
                if elem.attrib['encoding'] == 'CODE128':
                    bbcode = strclean(elem.text)
                    bbcode_prep = '{B%s' % bbcode
                    self.barcode(bbcode_prep, elem.attrib['encoding'],
                                 function_type='B')
                else:
                    self.barcode(strclean(elem.text),elem.attrib['encoding'])
                serializer.end_entity()

            elif elem.tag == 'cut':
                self.cut()
            elif elem.tag == 'partialcut':
                self.cut(mode='part')
            elif elem.tag == 'cashdraw':
                self.cashdraw(2)
                self.cashdraw(5)

            stylestack.pop()

        try:
            stylestack      = StyleStack()
            serializer      = XmlSerializer(self)
            root            = ET.fromstring(xml.encode('utf-8'))

            self._raw(stylestack.to_escpos())

            print_elem(stylestack,serializer,root)

            if 'open-cashdrawer' in root.attrib and root.attrib['open-cashdrawer'] == 'true':
                self.cashdraw(2)
                self.cashdraw(5)
            if not 'cut' in root.attrib or root.attrib['cut'] == 'true' :
                self.cut()

        except Exception as e:
            errmsg = str(e)+'\n'+'-'*48+'\n'+traceback.format_exc() + '-'*48+'\n'
            self.text(errmsg)
            self.cut()

            raise e


class TmpFile(UsbPrinter):
    def __init__(self, file="/tmp/printer"):
        self.file = file
        self.open()

    def open(self):
        self.fd = open(self.file, 'a')

        if self.fd is not None:
            print("File printer enabled")
        else:
            print("Unable to open file printer : %s" % self.file)

    def _raw(self, msg):
        """ Print any command sent in raw format """
        self.fd.write(msg)

    def __del__(self):
        """ Close Serial interface """
        if self.device is not None:
            self.device.close()

    def close(self):
        """ Close Serial interface """
        if self.device is not None:
            self.device.close()

# END Patch things needed to print in escpos


class EscposDriver(Thread):
    def __init__(self):
        Thread.__init__(self)
        self.queue = Queue()
        self.lock  = Lock()
        self.status = {'status':'connecting', 'messages':[]}

    def connected_usb_devices(self):
        connected = []

        # printers can either define bDeviceClass=7, or they can define one of
        # their interfaces with bInterfaceClass=7. This class checks for both.
        class FindUsbClass(object):
            def __init__(self, usb_class):
                self._class = usb_class
            def __call__(self, device):
                # first, let's check the device
                if device.bDeviceClass == self._class:
                    return True
                # transverse all devices and look through their interfaces to
                # find a matching class
                for cfg in device:
                    intf = usb.util.find_descriptor(cfg, bInterfaceClass=self._class)

                    if intf is not None:
                        return True

                return False

        printers = usb.core.find(find_all=True, custom_match=FindUsbClass(7))

        # if no printers are found after this step we will take the
        # first epson or star device we can find.
        # epson
        if not printers:
            printers = usb.core.find(find_all=True, idVendor=0x04b8)
        # star
        if not printers:
            printers = usb.core.find(find_all=True, idVendor=0x0519)

        for printer in printers:
            try:
                description = usb.util.get_string(printer, 256, printer.iManufacturer) + " " + usb.util.get_string(printer, 256, printer.iProduct)
            except Exception as e:
                _logger.error("Can not get printer description: %s" % (e.message or repr(e)))
                description = 'Unknown printer'
            connected.append({
                'vendor': printer.idVendor,
                'product': printer.idProduct,
                'name': description
            })

        return connected

    def lockedstart(self):
        with self.lock:
            if not self.isAlive():
                self.daemon = True
                self.start()

    def get_escpos_printer(self):
        # self.set_status('connected', 'Connected to printer')
        # return TmpFile('/tmp/printer')

        printers = self.connected_usb_devices()
        if len(printers) > 0:
            print_dev = UsbPrinter(printers[0]['vendor'], printers[0]['product'])
            self.set_status(
                'connected',
                "Connected to %s (in=0x%02x,out=0x%02x)" % (printers[0]['name'], print_dev.in_ep, print_dev.out_ep)
            )
            return print_dev
        else:
            self.set_status('disconnected','Printer Not Found')
            return None

    def get_status(self):
        self.push_task('status')
        return self.status

    def open_cashbox(self,printer):
        printer.cashdraw(2)
        printer.cashdraw(5)

    def set_status(self, status, message = None):
        _logger.info(status+' : '+ (message or 'no message'))
        if status == self.status['status']:
            if message != None and (len(self.status['messages']) == 0 or message != self.status['messages'][-1]):
                self.status['messages'].append(message)
        else:
            self.status['status'] = status
            if message:
                self.status['messages'] = [message]
            else:
                self.status['messages'] = []

        if status == 'error' and message:
            _logger.error('ESC/POS Error: '+message)
        elif status == 'disconnected' and message:
            _logger.warning('ESC/POS Device Disconnected: '+message)

    def run(self):
        printer = None
        if not escpos:
            _logger.error('ESC/POS cannot initialize, please verify system dependencies.')
            return
        while True:
            try:
                error = True
                timestamp, task, data = self.queue.get(True)
                printer = self.get_escpos_printer()

                if printer == None:
                    if task != 'status':
                        self.queue.put((timestamp,task,data))
                    error = False
                    time.sleep(5)
                    continue
                elif task == 'receipt':
                    if timestamp >= time.time() - 1 * 60 * 60:
                        self.print_receipt_body(printer,data)
                        printer.cut()
                elif task == 'xml_receipt':
                    if timestamp >= time.time() - 1 * 60 * 60:
                        printer.receipt(data)
                elif task == 'cashbox':
                    if timestamp >= time.time() - 12:
                        self.open_cashbox(printer)
                elif task == 'printstatus':
                    self.print_status(printer)
                elif task == 'status':
                    pass
                error = False

            # except NoDeviceError as e:
            #     _logger.exception('Exception!!!')
            #     print "No device found %s" %str(e)
            # except HandleDeviceError as e:
            #     print "Impossible to handle the device due to previous error %s" % str(e)
            # except TicketNotPrinted as e:
            #     print "The ticket does not seems to have been fully printed %s" % str(e)
            # except NoStatusError as e:
            #     print "Impossible to get the status of the printer %s" % str(e)
            except Exception as e:
                self.set_status('error', str(e))
                # errmsg = str(e) + '\n' + '-'*60+'\n' + traceback.format_exc() + '-'*60 + '\n'
                _logger.exception('Problem while processing task!');
            finally:
                if error:
                    self.queue.put((timestamp, task, data))
                if printer:
                    printer.close()

    def push_task(self,task, data = None):
        self.lockedstart()
        self.queue.put((time.time(),task,data))

    def print_status(self,eprint):
        localips = ['0.0.0.0','127.0.0.1','127.0.1.1']
        hosting_ap = os.system('pgrep hostapd') == 0
        ssid = subprocess.check_output('iwconfig 2>&1 | grep \'ESSID:"\' | sed \'s/.*"\\(.*\\)"/\\1/\'', shell=True).rstrip()
        mac = subprocess.check_output('ifconfig | grep -B 1 \'inet addr\' | grep -o \'HWaddr .*\' | sed \'s/HWaddr //\'', shell=True).rstrip()
        ips =  [ c.split(':')[1].split(' ')[0] for c in commands.getoutput("/sbin/ifconfig").split('\n') if 'inet addr' in c ]
        ips =  [ ip for ip in ips if ip not in localips ]
        eprint.text('\n\n')
        eprint.set(align='center',font='b',height=2,width=2)
        eprint.text('PosBox Status\n')
        eprint.text('\n')
        eprint.set(align='center')

        if hosting_ap:
            eprint.text('Wireless network:\nPosbox\n\n')
        elif ssid:
            eprint.text('Wireless network:\n' + ssid + '\n\n')

        if len(ips) == 0:
            eprint.text('ERROR: Could not connect to LAN\n\nPlease check that the PosBox is correc-\ntly connected with a network cable,\n that the LAN is setup with DHCP, and\nthat network addresses are available')
        elif len(ips) == 1:
            eprint.text('IP Address:\n'+ips[0]+'\n')
        else:
            eprint.text('IP Addresses:\n')
            for ip in ips:
                eprint.text(ip+'\n')

        if len(ips) >= 1:
            eprint.text('\nMAC Address:\n' + mac + '\n')
            eprint.text('\nHomepage:\nhttp://'+ips[0]+':8069\n')

        eprint.text('\n\n')
        eprint.cut()

    def print_receipt_body(self,eprint,receipt):

        def check(string):
            return string != True and bool(string) and string.strip()

        def price(amount):
            return ("{0:."+str(receipt['precision']['price'])+"f}").format(amount)

        def money(amount):
            return ("{0:."+str(receipt['precision']['money'])+"f}").format(amount)

        def quantity(amount):
            if math.floor(amount) != amount:
                return ("{0:."+str(receipt['precision']['quantity'])+"f}").format(amount)
            else:
                return str(amount)

        def printline(left, right='', width=40, ratio=0.5, indent=0):
            lwidth = int(width * ratio)
            rwidth = width - lwidth
            lwidth = lwidth - indent

            left = left[:lwidth]
            if len(left) != lwidth:
                left = left + ' ' * (lwidth - len(left))

            right = right[-rwidth:]
            if len(right) != rwidth:
                right = ' ' * (rwidth - len(right)) + right

            return ' ' * indent + left + right + '\n'

        def print_taxes():
            taxes = receipt['tax_details']
            for tax in taxes:
                eprint.text(printline(tax['tax']['name'],price(tax['amount']), width=40,ratio=0.6))

        # Receipt Header
        if receipt['company']['logo']:
            eprint.set(align='center')
            eprint.print_base64_image(receipt['company']['logo'])
            eprint.text('\n')
        else:
            eprint.set(align='center',type='b',height=2,width=2)
            eprint.text(receipt['company']['name'] + '\n')

        eprint.set(align='center',type='b')
        if check(receipt['company']['contact_address']):
            eprint.text(receipt['company']['contact_address'] + '\n')
        if check(receipt['company']['phone']):
            eprint.text('Tel:' + receipt['company']['phone'] + '\n')
        if check(receipt['company']['vat']):
            eprint.text('VAT:' + receipt['company']['vat'] + '\n')
        if check(receipt['company']['email']):
            eprint.text(receipt['company']['email'] + '\n')
        if check(receipt['company']['website']):
            eprint.text(receipt['company']['website'] + '\n')
        if check(receipt['header']):
            eprint.text(receipt['header']+'\n')
        if check(receipt['cashier']):
            eprint.text('-'*32+'\n')
            eprint.text('Served by '+receipt['cashier']+'\n')

        # Orderlines
        eprint.text('\n\n')
        eprint.set(align='center')
        for line in receipt['orderlines']:
            pricestr = price(line['price_display'])
            if line['discount'] == 0 and line['unit_name'] == 'Unit(s)' and line['quantity'] == 1:
                eprint.text(printline(line['product_name'],pricestr,ratio=0.6))
            else:
                eprint.text(printline(line['product_name'],ratio=0.6))
                if line['discount'] != 0:
                    eprint.text(printline('Discount: '+str(line['discount'])+'%', ratio=0.6, indent=2))
                if line['unit_name'] == 'Unit(s)':
                    eprint.text( printline( quantity(line['quantity']) + ' x ' + price(line['price']), pricestr, ratio=0.6, indent=2))
                else:
                    eprint.text( printline( quantity(line['quantity']) + line['unit_name'] + ' x ' + price(line['price']), pricestr, ratio=0.6, indent=2))

        # Subtotal if the taxes are not included
        taxincluded = True
        if money(receipt['subtotal']) != money(receipt['total_with_tax']):
            eprint.text(printline('','-------'));
            eprint.text(printline(_('Subtotal'),money(receipt['subtotal']),width=40, ratio=0.6))
            print_taxes()
            #eprint.text(printline(_('Taxes'),money(receipt['total_tax']),width=40, ratio=0.6))
            taxincluded = False


        # Total
        eprint.text(printline('','-------'));
        eprint.set(align='center',height=2)
        eprint.text(printline(_('         TOTAL'),money(receipt['total_with_tax']),width=40, ratio=0.6))
        eprint.text('\n\n');

        # Paymentlines
        eprint.set(align='center')
        for line in receipt['paymentlines']:
            eprint.text(printline(line['journal'], money(line['amount']), ratio=0.6))

        eprint.text('\n');
        eprint.set(align='center',height=2)
        eprint.text(printline(_('        CHANGE'),money(receipt['change']),width=40, ratio=0.6))
        eprint.set(align='center')
        eprint.text('\n');

        # Extra Payment info
        if receipt['total_discount'] != 0:
            eprint.text(printline(_('Discounts'),money(receipt['total_discount']),width=40, ratio=0.6))
        if taxincluded:
            print_taxes()
            #eprint.text(printline(_('Taxes'),money(receipt['total_tax']),width=40, ratio=0.6))

        # Footer
        if check(receipt['footer']):
            eprint.text('\n'+receipt['footer']+'\n\n')
        eprint.text(receipt['name']+'\n')
        eprint.text(      str(receipt['date']['date']).zfill(2)
                    +'/'+ str(receipt['date']['month']+1).zfill(2)
                    +'/'+ str(receipt['date']['year']).zfill(4)
                    +' '+ str(receipt['date']['hour']).zfill(2)
                    +':'+ str(receipt['date']['minute']).zfill(2) )


driver = EscposDriver()

driver.push_task('printstatus')

hw_proxy.drivers['escpos'] = driver

class EscposProxy(hw_proxy.Proxy):

    @http.route('/hw_proxy/open_cashbox', type='json', auth='none', cors='*')
    def open_cashbox(self):
        _logger.info('ESC/POS: OPEN CASHBOX')
        driver.push_task('cashbox')

    @http.route('/hw_proxy/print_receipt', type='json', auth='none', cors='*')
    def print_receipt(self, receipt):
        _logger.info('ESC/POS: PRINT RECEIPT')
        driver.push_task('receipt',receipt)

    @http.route('/hw_proxy/print_xml_receipt', type='json', auth='none', cors='*')
    def print_xml_receipt(self, receipt):
        _logger.info('ESC/POS: PRINT XML RECEIPT')
        driver.push_task('xml_receipt',receipt)

