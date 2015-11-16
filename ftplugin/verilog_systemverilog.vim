" Vim filetype plugin file
" Language:	SystemVerilog (superset extension of Verilog)

" Only do this when not done yet for this buffer
if exists("b:did_ftplugin")
  finish
endif

" Define include string
setlocal include=^\\s*`include

" Set omni completion function
set omnifunc=verilog_systemverilog#Complete

" Command definitions
command! -nargs=* VerilogErrorFormat call verilog_systemverilog#VerilogErrorFormat(<f-args>)
command!          VerilogFollowInstance call verilog_systemverilog#FollowInstanceTag(line('.'), col('.'))
command!          VerilogFollowPort call verilog_systemverilog#FollowInstanceSearchWord(line('.'), col('.'))
command!          VerilogGotoInstanceStart call verilog_systemverilog#GotoInstanceStart(line('.'), col('.'))

" Behaves just like Verilog
runtime! ftplugin/verilog.vim

" Store cpoptions
let oldcpo=&cpoptions
set cpo-=C

" Override matchit configurations
if exists("loaded_matchit")
  let b:match_ignorecase=0
  let b:match_words=
    \ '\<begin\>:\<end\>,' .
    \ '\<case\>\|\<casex\>\|\<casez\>:\<endcase\>,' .
    \ '`if\(n\)\?def\>:`elsif\>:`else\>:`endif\>,' .
    \ '\<module\>:\<endmodule\>,' .
    \ '\<if\>:\<else\>,' .
    \ '\<fork\>:\<join\(_any\|_none\)\?\>,' .
    \ '\<function\>:\<endfunction\>,' .
    \ '\<task\>:\<endtask\>,' .
    \ '\<specify\>:\<endspecify\>,' .
    \ '\<config\>:\<endconfig\>,' .
    \ '\<specify\>:\<endspecify\>,' .
    \ '\<generate\>:\<endgenerate\>,' .
    \ '\<primitive\>:\<endprimitive\>,' .
    \ '\<table\>:\<endtable\>,' .
    \ '\<class\>:\<endclass\>,' .
    \ '\<checker\>:\<endchecker\>,' .
    \ '\<interface\>:\<endinterface\>,' .
    \ '\<clocking\>:\<endclocking\>,' .
    \ '\<covergroup\>:\<endgroup\>,' .
    \ '\<package\>:\<endpackage\>,' .
    \ '\<program\>:\<endprogram\>,' .
    \ '\<property\>:\<endproperty\>,' .
    \ '\<sequence\>:\<endsequence\>'
endif

" Configure tagbar
" This requires a recent version of universal-ctags
let g:tagbar_type_verilog_systemverilog = {
    \ 'ctagstype'   : 'SystemVerilog',
    \ 'kinds'       : [
        \ 'b:blocks:1:1',
        \ 'c:constants:1:0',
        \ 'e:events:1:0',
        \ 'f:functions:1:1',
        \ 'm:modules:0:1',
        \ 'n:nets:1:0',
        \ 'p:ports:1:0',
        \ 'r:registers:1:0',
        \ 't:tasks:1:1',
        \ 'A:assertions:1:1',
        \ 'C:classes:0:1',
        \ 'V:covergroups:0:1',
        \ 'I:interfaces:0:1',
        \ 'M:modport:0:1',
        \ 'K:packages:0:1',
        \ 'P:programs:0:1',
        \ 'R:properties:0:1',
        \ 'T:typedefs:0:1'
    \ ],
    \ 'sro'         : '.',
    \ 'kind2scope'  : {
        \ 'm' : 'module',
        \ 'b' : 'block',
        \ 't' : 'task',
        \ 'f' : 'function',
        \ 'C' : 'class',
        \ 'V' : 'covergroup',
        \ 'I' : 'interface',
        \ 'K' : 'package',
        \ 'P' : 'program',
        \ 'R' : 'property'
    \ },
\ }

" Restore cpoptions
let &cpoptions=oldcpo

" Raise warning if smartindent is defined
if &smartindent
    echohl WarningMsg
    redraw
    echo "Option 'smartindent' should not be used in Verilog syntax, use 'autoindent' instead."
endif

" vi: sw=2 sts=2:
