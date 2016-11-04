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
    let g:verilog_disable_indent_lst = "module,eos"
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

        let test_result = TestEfm('iverilog',  1, check_uvm) || test_result
        let test_result = TestEfm('verilator', 1, check_uvm) || test_result
        let test_result = TestEfm('verilator', 3, check_uvm) || test_result
        let test_result = TestEfm('ncverilog', 1, check_uvm) || test_result
        let test_result = TestEfm('ncverilog', 3, check_uvm) || test_result
        let test_result = TestEfm('spyglass',  1, check_uvm) || test_result
    endfor

    " Check test results and exit accordingly
    if test_result
        cquit
    else
        qall!
    endif
endfunction

"-----------------------------------------------------------------------
" Syntax test
"-----------------------------------------------------------------------
function! RunTestSyntax()
    set nomore "Disable pager to avoid issues with Travis

    silent view test/syntax.sv

    " Generate HTML version of the file
    let g:html_line_ids=0
    let g:html_number_lines=0
    TOhtml
    " Clean up resulting HTML to minimize differences with other version
    " of TOhtml script
    1,/<body>/-1delete
    /<\/body>/+1,$delete
    %s/ id='vimCodeElement'//
    " Write final buffer
    w! test/syntax.sv.new.html

    " Compare with reference
    silent let output = system('diff test/syntax.sv.html test/syntax.sv.new.html')

    if output == ""
        echo 'Syntax test passed'
        let test_result = 0
    else
        echo 'Syntax test failed'
        let test_result = 1
    endif

    " Check test results and exit accordingly
    if test_result
        cquit
    else
        qall!
    endif
endfunction

" vi: set expandtab softtabstop=4 shiftwidth=4:
