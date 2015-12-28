"-----------------------------------------------------------------------
" Run tests
"-----------------------------------------------------------------------
unlet! g:verilog_dont_deindent_eos
let test_result=0

"-----------------------------------------------------------------------
" Syntax folding test
"-----------------------------------------------------------------------
" Enable all syntax folding
let g:verilog_syntax_fold="all"
set foldmethod=syntax
set noautochdir

" Open syntax fold test file in read-only mode
view test/folding.v

" Verify folding
let test_result=TestFold() || test_result
echo ''

" Test with "block_nested"
let g:verilog_syntax_fold="all,block_nested"
silent view!
let test_result=TestFold(1) || test_result
echo ''

"-----------------------------------------------------------------------
" Syntax indent test
"-----------------------------------------------------------------------
" Open syntax indent test file in read-only mode
silent edit test/indent.sv

" Verify folding
let test_result=TestIndent() || test_result
echo ''

silent edit!

"-----------------------------------------------------------------------
" Check test results and exit accordingly
"-----------------------------------------------------------------------
if test_result
  cquit
else
  quit
endif
