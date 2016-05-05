"-----------------------------------------------------------------------
" Syntax folding test
"-----------------------------------------------------------------------
function! RunTestFold()
    let test_result=0

    " Enable all syntax folding
    let g:verilog_syntax_fold_lst="all"
    set foldmethod=syntax
    set noautochdir

    " Open syntax fold test file in read-only mode
    silent view test/folding.v

    " Verify folding
    let test_result=TestFold(0) || test_result
    echo ''

    " Test with "block_nested"
    let g:verilog_syntax_fold_lst="all,block_nested"
    silent view!
    let test_result=TestFold(1) || test_result
    echo ''

    " Test with "block_named"
    let g:verilog_syntax_fold_lst="all,block_named"
    silent view!
    let test_result=TestFold(2) || test_result
    echo ''

    " Check test results and exit accordingly
    if test_result
        cquit
    else
        qall!
    endif
endfunction

"-----------------------------------------------------------------------
" Syntax indent test
"-----------------------------------------------------------------------
function! RunTestIndent()
    unlet! g:verilog_dont_deindent_eos
    let g:verilog_disable_indent_lst = "module"
    let test_result=0

    " Open syntax indent test file
    silent edit test/indent.sv

    " Verify indent
    let test_result=TestIndent() || test_result
    echo ''
    silent edit!

    " Test again with 'ignorecase' enabled
    setlocal ignorecase
    let test_result=TestIndent() || test_result
    echo ''
    silent edit!

    " Make file read-only to guarantee that vim quits with exit status 0
    silent view!

    " Check test results and exit accordingly
    if test_result
        cquit
    else
        qall!
    endif
endfunction

"-----------------------------------------------------------------------
" Error format test
"-----------------------------------------------------------------------
function! RunTestEfm()
    let test_result=0

    set nomore "Disable pager to avoid issues with Travis

    let g:verilog_efm_quickfix_clean = 1

    for check_uvm in [0, 1]
        if check_uvm
            let g:verilog_efm_uvm_lst = 'all'
        else
            unlet! g:verilog_efm_uvm_lst
        endif

        silent view test/errorformat.txt
        let test_result=TestEfm('iverilog', 1, check_uvm) || test_result
        echo ''
    endfor

    " Check test results and exit accordingly
    if test_result
        cquit
    else
        qall!
    endif
endfunction

" vi: set expandtab softtabstop=4 shiftwidth=4:
