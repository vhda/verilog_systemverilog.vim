// Code based on: https://github.com/vhda/verilog_systemverilog.vim/issues/2
class z;

    typedef struct {
        real a;
        int b;
        int c;
        real d; } ts;

    ts s[];

    typedef struct {
        real a;
        int b;
        int c;
        real d;
    } ts2;

    ts2 t[];

    int unsigned cnt=0;

    function new();
        super.new();
    endfunction;

endclass
