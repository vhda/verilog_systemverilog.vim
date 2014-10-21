" Vim filetype plugin file
" Language:	SystemVerilog (superset extension of Verilog)
" Maintainer:	Amit Sethi <amitrajsethi@yahoo.com>
" Last Change:	Tue Jun 26 08:56:34 IST 2006
" Version: 1.0

" Only do this when not done yet for this buffer
if exists("b:did_ftplugin")
  finish
endif

" Define include string
setlocal include=^\s*`include

" Behaves just like Verilog
runtime! ftplugin/verilog.vim

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
