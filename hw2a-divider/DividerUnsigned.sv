/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// quotient = dividend / divisor

module DividerUnsigned (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    // TODO: your code here

    wire [31:0] remainder [0:32];
    wire [31:0] quotient  [0:32];
    wire [31:0] dividend  [0:32];

    assign dividend[0] = i_dividend;
    assign quotient[0]  = 32'd0;
    assign remainder[0] = 32'd0;

    genvar i;
    generate
        for (i = 0; i < 32; i = i + 1) begin : divider_loop
            DividerOneIter divider_one_iter (
                .i_dividend (dividend[i]),
                .i_divisor (i_divisor),
                .i_remainder (remainder[i]),
                .i_quotient (quotient[i]),
                .o_dividend (dividend[i+1]),
                .o_remainder (remainder[i+1]),
                .o_quotient (quotient[i+1])
            );
        end
    endgenerate

    assign o_remainder = remainder[32];
    assign o_quotient  = quotient[32];  

endmodule


module DividerOneIter (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    input  wire [31:0] i_remainder,
    input  wire [31:0] i_quotient,
    output wire [31:0] o_dividend,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);
  /*
    for (int i = 0; i < 32; i++) {
        remainder = (remainder << 1) | ((dividend >> 31) & 0x1);
        if (remainder < divisor) {
            quotient = (quotient << 1);
        } else {
            quotient = (quotient << 1) | 0x1;
            remainder = remainder - divisor;
        }
        dividend = dividend << 1;
    }
    */

    // TODO: your code here


    wire [31:0]shifted_remainder;

    assign shifted_remainder = (i_remainder << 1) | ((i_dividend >> 31) & 32'h1);
    assign o_quotient = (shifted_remainder < i_divisor) ? (i_quotient << 1) : ((i_quotient << 1) | 32'h1);
    assign o_remainder = (shifted_remainder < i_divisor) ? shifted_remainder : (shifted_remainder - i_divisor);
    assign o_dividend = i_dividend << 1;

endmodule
