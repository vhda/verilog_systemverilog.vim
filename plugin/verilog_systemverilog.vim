" Global plugin settings
let g:verilog_disable_indent_lst="eos,standalone"

" Command definitions
command! -nargs=* VerilogErrorFormat call verilog_systemverilog#VerilogErrorFormat(<f-args>)
command!          VerilogFollowInstance call verilog_systemverilog#FollowInstanceTag(line('.'), col('.'))
command!          VerilogReturnInstance call verilog_systemverilog#ReturnFromInstanceTag()
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

" vi: set expandtab softtabstop=4 shiftwidth=4:
