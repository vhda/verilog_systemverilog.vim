" Vim filetype plugin file
" Language:	SystemVerilog (superset extension of Verilog)

" Only do this when not done yet for this buffer
if exists("b:did_ftplugin")
    finish
endif

au BufNewFile,BufRead *.v,*.vh,*.sv,*.svi,*.svh set filetype=verilog_systemverilog
