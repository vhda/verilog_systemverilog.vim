module mod (
    input  wire     [7:0] in1,
    input  wire           in2,
    output reg            out
);

function test (
    input a,
    input b,
    output z
);
endfunction

endmodule

class myclass;
    logic variable;

    function method (input a, input b);
    endfunction : method

    task atask (input a, output x);
    endtask : atask

endclass : myclass
