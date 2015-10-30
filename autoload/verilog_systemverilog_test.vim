function! verilog_systemverilog_test#TestFold()
    let fail = 0
    let fail_lines = ''
    let linenr = 0
    while linenr < line("$")
        let linenr += 1
        let line = getline(linenr)
        let line = substitute(line, '.*<\(\d*\)>.*', '\1', '')
        let level = foldlevel(linenr)
        if (level == line)
        else
            let fail = 1
            if (fail_lines == '')
                let fail_lines = linenr
            else
                let fail_lines = fail_lines.','.linenr
            endif
        endif
    endwhile

    if (fail == 1)
        echom 'Fold test failed:'
        echom fail_lines
        return 1
    else
        echom 'Fold test passed'
        return 0
    endif

endfunction
