// Code based on: https://github.com/vhda/verilog_systemverilog.vim/issues/2
class z;

    // this is a comment
    // -----------------
    typedef struct {
        real a;
        int b;
        int c;
        real d; } ts;

    ts s[];

    // if there are
    // more comments
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

    // Code from: https://github.com/vhda/verilog_systemverilog.vim/issues/4
    task run_phase(uvm_phase phase);

        assert(my_seq.randomize());
        my_seq.start(low_sequencer_h);

        assert(my_seq.randomize() with {Nr==6;});
        my_seq.start(low_sequencer_h);

        assert(my_seq.randomize() with
        {Nr==6; Time==8;});
        my_seq.start(low_sequencer_h);

    endtask

endclass

// vim: set sts=4 sw=4:
