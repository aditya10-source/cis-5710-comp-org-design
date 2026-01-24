`timescale 1ns / 1ps

/**
 * @param a first 1-bit input
 * @param b second 1-bit input
 * @param g whether a and b generate a carry
 * @param p whether a and b would propagate an incoming carry
 */
module gp1(input wire a, b,
           output wire g, p);
   assign g = a & b;
   assign p = a | b;
endmodule

/**
 * Computes aggregate generate/propagate signals over a 4-bit window.
 * @param gin incoming generate signals
 * @param pin incoming propagate signals
 * @param cin the incoming carry
 * @param gout whether these 4 bits internally would generate a carry-out (independent of cin)
 * @param pout whether these 4 bits internally would propagate an incoming carry from cin
 * @param cout the carry outs for the low-order 3 bits
 */
module gp4(input wire [3:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [2:0] cout);

   // TODO: your code here
   // Received g3:0  p3:0 immediately

   // c4 = g3:0 + p3:0 * cin
   assign pout = (&pin);
   assign gout = gin[3] | (pin[3] & gin[2]) | ((&pin[3:2]) & gin[1]) | ((&pin[3:1]) & gin[0]);

   // Internal carries (into bits 1..3)
    assign cout[0] = gin[0] | (pin[0] & cin);                         // c1
    assign cout[1] = gin[1] | (pin[1] & gin[0]) | ((&pin[1:0]) & cin);         // c2
    assign cout[2] = gin[2] | (pin[2] & gin[1]) | ((&pin[2:1])& gin[0]) |
                     ((&pin[2:0]) & cin);                     // c3

endmodule

/** Same as gp4 but for an 8-bit window instead */
module gp8(input wire [7:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [6:0] cout);

   // TODO: your code here
   // Received g7:0  p7:0 immediately

   wire g0 = gin[0], g1 = gin[1], g2 = gin[2], g3 = gin[3],
        g4 = gin[4], g5 = gin[5], g6 = gin[6], g7 = gin[7];
   wire p0 = pin[0], p1 = pin[1], p2 = pin[2], p3 = pin[3],
        p4 = pin[4], p5 = pin[5], p6 = pin[6], p7 = pin[7];

   // c8 = g7:0 + p7:0 * cin
   assign pout = (&pin);
   assign gout = gin[7] | (pin[7] & gin[6]) | ((&pin[7:6]) & gin[5]) | (&pin[7:5] & gin[4]) |
                 ((&pin[7:4]) & gin[3]) | ((&pin[7:3]) & gin[2]) |
                 ((&pin[7:2]) & gin[1]) |
                 ((&pin[7:1]) & gin[0]);

   // Internal carries (into bits 1..7)
   assign cout[0] = gin[0] | (pin[0] & cin); // c1
   assign cout[1] = gin[1] | (pin[1] & gin[0]) | ((&pin[1:0]) & cin); // c2
   assign cout[2] = gin[2] | (pin[2] & gin[1]) | ((&pin[2:1]) & gin[0]) |
                    ((&pin[2:0]) & cin); // c3
   assign cout[3] = gin[3] | (pin[3] & gin[2]) | ((&pin[3:2]) & gin[1]) |
                    ((&pin[3:1])& gin[0]) |
                    ((&pin[3:0]) & cin); // c4
   assign cout[4] = gin[4] | (pin[4] & gin[3]) | ((&pin[4:3]) & gin[2]) |
                    ((&pin[4:2]) & gin[1]) |
                    ((&pin[4:1]) & gin[0]) |
                    ((&pin[4:0]) & cin); // c5
   assign cout[5] = gin[5] | (pin[5] & gin[4]) | ((&pin[5:4]) & gin[3]) |
                    ((&pin[5:3]) & gin[2]) |
                    ((&pin[5:2]) & gin[1]) |
                    ((&pin[5:1]) & gin[0]) |
                    ((&pin[5:0]) & cin); // c6
   assign cout[6] = gin[6] | (pin[6] & gin[5]) | ((&pin[6:5]) & gin[4]) |
                    ((&pin[6:4]) & gin[3]) |
                    ((&pin[6:3]) & gin[2]) |
                    ((&pin[6:2]) & gin[1]) |
                    ((&pin[6:1]) & gin[0]) |
                    ((&pin[6:0]) & cin); // c7

endmodule

module CarryLookaheadAdder
  (input wire [31:0]  a, b,
   input wire         cin,
   output wire [31:0] sum);

   // TODO: your code here
   wire [31:0] g, p; // generate and propagate signals for each bit

   genvar i;
   generate
      for (i = 0; i < 32; i = i + 1) begin : gp_gen
         gp1 gp1_inst(.a(a[i]), .b(b[i]), .g(g[i]), .p(p[i]));
      end
   endgenerate

   // 8 blocks of 4-bit: each gp4 returns block G/P and internal carries
   wire [7:0] G4, P4;

   // Carry into each 4-bit block: cblk[k] = carry into bit (4*k)
   wire [7:0] cblk;
   assign cblk[0] = cin;

   // Carries into blocks 1..7 (i.e., into bits 4,8,...,28)
   wire [6:0] cblk_next;
   wire pout_unused, gout_unused;

   // IMPORTANT: This gp8 uses the 8 block G/Ps as its "bits"
   // and produces carry-ins for blocks 1..7.
   gp8 u_gp8(
      .gin (G4),
      .pin (P4),
      .cin (cin),
      .gout(pout_unused),     // unused
      .pout(gout_unused),     // unused
      .cout(cblk_next)
   );

   // Stitch: cblk[1]..cblk[7]
   generate
      for (i = 1; i < 8; i = i + 1) begin : blk_carry_stitch
         assign cblk[i] = cblk_next[i-1];
      end
   endgenerate

   // Now build each 4-bit block with gp4, then compute sums.
   genvar k;
   generate
      for (k = 0; k < 8; k = k + 1) begin : blk4
         wire [2:0] c_in; // carries into bits 1..3 of this 4-bit block

         gp4 u_gp4(
            .gin ( g[k*4 +: 4] ),
            .pin ( p[k*4 +: 4] ),
            .cin ( cblk[k]      ),
            .gout( G4[k]        ),
            .pout( P4[k]        ),
            .cout( c_in         )
         );

         // Carry into each bit of the block:
         // bit0 uses cblk[k], bits1..3 use c_in[0..2]
         wire c0 = cblk[k];
         wire c1 = c_in[0];
         wire c2 = c_in[1];
         wire c3 = c_in[2];

         // SUM LOGIC:
         // With your gp1 propagate definition p = a|b,
         // the correct sum is: sum = a ^ b ^ carry_in (NOT p ^ carry_in).
         assign sum[k*4 + 0] = a[k*4 + 0] ^ b[k*4 + 0] ^ c0;
         assign sum[k*4 + 1] = a[k*4 + 1] ^ b[k*4 + 1] ^ c1;
         assign sum[k*4 + 2] = a[k*4 + 2] ^ b[k*4 + 2] ^ c2;
         assign sum[k*4 + 3] = a[k*4 + 3] ^ b[k*4 + 3] ^ c3;
      end
   endgenerate

endmodule