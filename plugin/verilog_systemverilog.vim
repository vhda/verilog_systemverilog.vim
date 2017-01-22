" Global plugin settings
let g:verilog_disable_indent="eos"

" Command definitions
command! -nargs=* VerilogErrorFormat call verilog_systemverilog#VerilogErrorFormat(<f-args>)
command!          VerilogFollowInstance call verilog_systemverilog#FollowInstanceTag(line('.'), col('.'))
command!          VerilogFollowPort call verilog_systemverilog#FollowInstanceSearchWord(line('.'), col('.'))
command!          VerilogGotoInstanceStart call verilog_systemverilog#GotoInstanceStart(line('.'), col('.'))
command! -nargs=+ -complete=customlist,verilog_systemverilog#CompleteCommand
            \ VerilogFoldingAdd
            \ call verilog_systemverilog#PushToVariable('verilog_syntax_fold_lst', '<args>')
command! -nargs=+ -complete=customlist,verilog_systemverilog#CompleteCommand
            \ VerilogFoldingRemove
            \ call verilog_systemverilog#PopFromVariable('verilog_syntax_fold_lst', '<args>')
command! -nargs=+ -complete=customlist,verilog_systemverilog#CompleteCommand
            \ VerilogDisableIndentAdd
            \ call verilog_systemverilog#PushToVariable('verilog_disable_indent_lst', '<args>')
command! -nargs=+ -complete=customlist,verilog_systemverilog#CompleteCommand
            \ VerilogDisableIndentRemove
            \ call verilog_systemverilog#PopFromVariable('verilog_disable_indent_lst', '<args>')
command! -nargs=+ -complete=customlist,verilog_systemverilog#CompleteCommand
            \ VerilogErrorUVMAdd
            \ call verilog_systemverilog#PushToVariable('verilog_efm_uvm_lst', '<args>')
command! -nargs=+ -complete=customlist,verilog_systemverilog#CompleteCommand
            \ VerilogErrorUVMRemove
            \ call verilog_systemverilog#PopFromVariable('verilog_efm_uvm_lst', '<args>')

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

" vi: set expandtab softtabstop=4 shiftwidth=4:
