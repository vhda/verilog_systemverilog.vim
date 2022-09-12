" Vim filetype plugin file
" Language:	SystemVerilog (superset extension of Verilog)

" Only do this when not done yet for this buffer
if exists("b:did_ftplugin")
  finish
endif

" Define include string
setlocal include=^\\s*`include

" Set omni completion function
setlocal omnifunc=verilog_systemverilog#Complete

" Store cpoptions
let oldcpo=&cpoptions
set cpo-=C

" Undo the plugin effect
let b:undo_ftplugin = "setlocal fo< com< tw<"
    \ . "| unlet! b:browsefilter b:match_ignorecase b:match_words"

" Set 'formatoptions' to break comment lines but not other lines,
" and insert the comment leader when hitting <CR> or using "o".
setlocal fo-=t fo+=croqlm1

" Set 'comments' to format dashed lists in comments.
setlocal comments=sO:*\ -,mO:*\ \ ,exO:*/,s1:/*,mb:*,ex:*/,://

" Win32 and GTK can filter files in the browse dialog
if (has("gui_win32") || has("gui_gtk")) && !exists("b:browsefilter")
  let b:browsefilter = ""
        \ . "Verilog Family Source Files\t*.v;*.vh;*.vp;*.sv;*.svh;*.svi;*.svp\n"
        \ . "Verilog Source Files (*.v *.vh)\t*.v;*.vh\n"
        \ . "SystemVerilog Source Files (*.sv *.svh *.svi *.sva)\t*.sv;*.svh;*.svi;*.sva\n"
        \ . "Protected Files (*.vp *.svp)\t*.vp;*.svp\n"
        \ . "All Files (*.*)\t*.*\n"
endif
" Override matchit configurations
if exists("loaded_matchit")
  let b:match_ignorecase=0
  let b:match_words=
    \ '\<begin\>:\<end\>,' .
    \ '\<case\>\|\<casex\>\|\<casez\>:\<endcase\>,' .
    \ '`if\(n\)\?def\>:`elsif\>:`else\>:`endif\>,' .
    \ '\<module\>:\<endmodule\>,' .
    \ '\<if\>:\<else\>,' .
    \ '\<fork\>\s*;\@!$:\<join\(_any\|_none\)\?\>,' .
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

" fix for Nvim 0.72 error alm when open .v file
" for nvim (use :scriptname) execte systax/verilog_systemverilog.vim
" indentent/verilog_systemverilog.vim a little bit earlier,
" exectue plugin/verilog_systemverilog.vim latter,
" <<move form plugin/verilog_systemverilog.vim>> to
" <<ftplugin/verilog_systemverilog.vim>>
"
" Configure tagbar
if !exists("g:tagbar_type_verilog_systemverilog")
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
endif

" Define regular expressions for Verilog/SystemVerilog statements
let s:verilog_function_task_dequalifier =
    \  '\%('
    \ .    '\%('
    \ .        'extern\s\+\%(\%(pure\s\+\)\?virtual\s\+\)\?'
    \ .        '\|'
    \ .        'pure\s\+virtual\s\+'
    \ .        '\|'
    \ .        'import\s\+\"DPI\%(-[^\"]\+\)\?\"\s\+\%(context\s\+\)\?'
    \ .    '\)'
    \ .    '\%(\%(static\|protected\|local\)\s\+\)\?'
    \ .'\)'

let g:verilog_syntax = {
      \ 'assign'      : [{
                        \ 'match_start' : '[^><=!]\zs<\?=\%(=\)\@!',
                        \ 'match_end'   : '[;,]',
                        \ 'highlight'   : 'verilogOperator',
                        \ 'syn_argument': 'transparent contains=@verilogBaseCluster',
                        \ }],
      \ 'attribute'   : [{
                        \ 'match_start' : '\%(@\s*\)\@<!(\*',
                        \ 'match_end'   : '\*)',
                        \ 'highlight'   : 'verilogDirective',
                        \ 'syn_argument': 'transparent keepend contains=verilogComment,verilogNumber,verilogOperator,verilogString',
                        \ }],
      \ 'baseCluster' : [{
                        \ 'cluster'     : 'verilogComment,verilogNumber,verilogOperator,verilogString,verilogConstant,verilogGlobal,verilogMethod,verilogObject,verilogConditional,verilogIfdefContainer'
                        \ }],
      \ 'block'       : [{
                        \ 'match_start' : '\<begin\>',
                        \ 'match_end'   : '\<end\>',
                        \ 'syn_argument': 'transparent',
                        \ }],
      \ 'block_named' : [{
                        \ 'match_start' : '\<begin\>\s*:\s*\w\+',
                        \ 'match_end'   : '\<end\>',
                        \ 'syn_argument': 'transparent',
                        \ }],
      \ 'class'       : [{
                        \ 'match_start' : '\<class\>',
                        \ 'match_end'   : '\<endclass\>',
                        \ 'highlight'   : 'verilogStatement',
                        \ 'syn_argument': 'transparent',
                        \ }],
      \ 'clocking'    : [{
                        \ 'match_start' : '\<clocking\>',
                        \ 'match_end'   : '\<endclocking\>',
                        \ 'highlight'   : 'verilogStatement',
                        \ 'syn_argument': 'transparent keepend',
                        \ }],
      \ 'comment'     : [{
                        \ 'match'       : '//.*',
                        \ 'syn_argument': 'contains=verilogTodo,verilogDirective,@Spell'
                        \ },
                        \ {
                        \ 'match_start' : '/\*',
                        \ 'match_end'   : '\*/',
                        \ 'syn_argument': 'contains=verilogTodo,verilogDirective,@Spell keepend extend'
                        \ }],
      \ 'covergroup'  : [{
                        \ 'match_start' : '\<covergroup\>',
                        \ 'match_end'   : '\<endgroup\>',
                        \ 'highlight'   : 'verilogStatement',
                        \ 'syn_argument': 'transparent keepend',
                        \ }],
      \ 'define'      : [{
                        \ 'match_start' : '`define\>',
                        \ 'match_end'   : '\(\\\s*\)\@<!$',
                        \ 'syn_argument': 'contains=@verilogBaseCluster'
                        \ }],
      \ 'export'      : [{
                        \ 'match_start' : '\<export\>',
                        \ 'match_end'   : '\<task\|function\>',
                        \ 'highlight'   : 'verilogStatement',
                        \ 'syn_argument': 'transparent contains=ALLBUT,verilogFunction,verilogTask',
                        \ }],
      \ 'expression'  : [{
                        \ 'match_start' : '(',
                        \ 'match_end'   : ')',
                        \ 'highlight'   : 'verilogOperator',
                        \ 'syn_argument': 'transparent contains=@verilogBaseCluster,verilogExpression,verilogStatement',
                        \ 'no_fold'     : '1',
                        \ }],
      \ 'function'    : [{
                        \ 'match_start' : s:verilog_function_task_dequalifier.'\@<!\<function\>',
                        \ 'match_end'   : '\<endfunction\>',
                        \ 'highlight'   : 'verilogStatement',
                        \ 'syn_argument': 'transparent keepend',
                        \ }],
      \ 'instance'    : [{
                        \ 'match_start' : '^\s*\zs\w\+\%(\s*#\s*(\%(.*)\s*\w\+\s*;\)\@!\|\s\+\%(\<if\>\)\@!\w\+\s*(\)',
                        \ 'match_end'   : ';',
                        \ 'syn_argument': 'transparent keepend contains=verilogListParam,verilogStatement,@verilogBaseCluster',
                        \ }],
      \ 'interface'   : [{
                        \ 'match_start' : '\%(\<virtual\s\+\)\@<!\<interface\>\%(\s\+class\)\@!',
                        \ 'match_end'   : '\<endinterface\>',
                        \ 'highlight'   : 'verilogStatement',
                        \ 'syn_argument': 'transparent keepend',
                        \ }],
      \ 'module'      : [{
                        \ 'match_start' : '\<\%(extern\s\+\)\@<!\<module\>',
                        \ 'match_end'   : '\<endmodule\>',
                        \ 'highlight'   : 'verilogStatement',
                        \ 'syn_argument': 'transparent keepend contains=ALLBUT,verilogInterface',
                        \ }],
      \ 'property'    : [{
                        \ 'match_start' : '\<\%(\%(assert\|assume\|cover\|restrict\)\s\+\)\@<!\<property\>',
                        \ 'match_end'   : '\<endproperty\>',
                        \ 'highlight'   : 'verilogStatement',
                        \ 'syn_argument': 'transparent keepend',
                        \ }],
      \ 'prototype'   : [{
                        \ 'match'       : s:verilog_function_task_dequalifier.'\@<=\<\%(task\|function\)\>',
                        \ }],
      \ 'sequence'    : [{
                        \ 'match_start' : '\<\%(cover\s\+\)\@<!\<sequence\>',
                        \ 'match_end'   : '\<endsequence\>',
                        \ 'highlight'   : 'verilogStatement',
                        \ 'syn_argument': 'transparent keepend',
                        \ }],
      \ 'specify'     : [{
                        \ 'match_start' : '\<specify\>',
                        \ 'match_end'   : '\<endspecify\>',
                        \ 'highlight'   : 'verilogStatement',
                        \ 'syn_argument': 'transparent keepend',
                        \ }],
      \ 'statement'   : [{
                        \ 'match'       : '\<\%(interface\|property\|sequence\|class\)\>',
                        \ }],
      \ 'task'        : [{
                        \ 'match_start' : s:verilog_function_task_dequalifier.'\@<!\<task\>',
                        \ 'match_end'   : '\<endtask\>',
                        \ 'highlight'   : 'verilogStatement',
                        \ 'syn_argument': 'transparent keepend',
                        \ }],
      \ 'typedef'     : [{
                        \ 'match_start' : '\<typedef\>',
                        \ 'match_end'   : '\ze;',
                        \ 'highlight'   : 'verilogTypeDef',
                        \ 'syn_argument': 'transparent keepend contains=ALLBUT,verilogClass',
                        \ }],
      \ }
" Restore cpoptions
let &cpoptions=oldcpo
unlet oldcpo

" Raise warning if smartindent is defined
if &smartindent
    echohl WarningMsg
    redraw
    echo "Option 'smartindent' should not be used in Verilog syntax, use 'autoindent' instead."
endif

" vi: set expandtab softtabstop=2 shiftwidth=2:
