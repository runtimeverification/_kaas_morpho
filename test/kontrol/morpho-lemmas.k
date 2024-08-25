requires "foundry.md"

module MORPHO-LEMMAS
    imports EVM
    imports FOUNDRY
    imports INT-SYMBOLIC
    imports MAP-SYMBOLIC
    imports SET-SYMBOLIC

    syntax StepSort ::= Int
                      | Bool
                      | Bytes
                      | Map
                      | Set
 // -------------------------

    syntax KItem ::= runLemma ( StepSort )
                   | doneLemma( StepSort )
 // --------------------------------------
    rule <k> runLemma(T) => doneLemma(T) ... </k>

    rule C <=Int A *Int B => C /Int A <=Int B
      requires 0 <=Int C andBool 0 <Int A
       andBool C modInt A ==Int 0
       [simplification(40), concrete(C, A), preserves-definedness]

    rule A ==Int B => false
      requires 0 <=Int A andBool B <Int 0
      [simplification, concrete(B)]

    rule 0 <=Int A -Int B => B <=Int A
      [simplification, symbolic(A, B)]

    rule ( ( A *Int B ) +Int C ) /Int D => ( ( ( A /Int 10 ) *Int B ) +Int ( ( D /Int 10 ) -Int 1 ) ) /Int ( D /Int 10 )
      requires 0 <=Int A andBool 0 <Int D
       andBool A modInt 10 ==Int 0 andBool D modInt 10 ==Int 0 andBool C ==Int D -Int 1
       [simplification, concrete(A, C, D), preserves-definedness]

    rule [asWord-lt-concat-left]:
      #asWord ( BA1 +Bytes BA2 ) <Int X => #asWord ( BA1 ) <Int X /Int ( 2 ^Int ( 8 *Int lengthBytes ( BA2 ) ) )
      requires X modInt ( 2 ^Int ( 8 *Int lengthBytes ( BA2 ) ) ) ==Int 0
      [simplification, preserves-definedness]

endmodule

module MORPHO-LEMMAS-SPEC
    imports MORPHO-LEMMAS

    claim [zero-lt-left]:
      <k> runLemma (
        0 <Int ( ( VV2_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV1_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) /Int 1000000000000000000000000000000000000 )
      ) => doneLemma (
        1000000000000000000000000000000000000 <=Int ( VV2_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV1_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) )
      ) ... </k>
      requires 100 <=Int VV1_amountBorrowed_114b9705:Int
       andBool 10000000000 <=Int VV2_priceCollateral_114b9705:Int
       andBool VV1_amountBorrowed_114b9705:Int <=Int 10000000000000000000000000000
       andBool VV2_priceCollateral_114b9705:Int <=Int 10000000000000000000000000000000000000000
       andBool ( pow128 *Int VV2_priceCollateral_114b9705:Int ) <=Int ( ( VV2_priceCollateral_114b9705:Int +Int ( 1000000000000000000000000000000000000 *Int ( ( ( 1000000000000000000 *Int VV1_amountBorrowed_114b9705:Int ) +Int 799999999999999999 ) /Int 800000000000000000 ) ) ) +Int -1 )


    claim [left-gt-zero]:
      <k> runLemma (
        ( ( VV2_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV1_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) /Int 1000000000000000000000000000000000000 ) >Int 0
      ) => doneLemma (
        1000000000000000000000000000000000000 <=Int ( VV2_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV1_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) )
      ) ... </k>
      requires 100 <=Int VV1_amountBorrowed_114b9705:Int
       andBool 10000000000 <=Int VV2_priceCollateral_114b9705:Int
       andBool VV1_amountBorrowed_114b9705:Int <=Int 10000000000000000000000000000
       andBool VV2_priceCollateral_114b9705:Int <=Int 10000000000000000000000000000000000000000
       andBool ( pow128 *Int VV2_priceCollateral_114b9705:Int ) <=Int ( ( VV2_priceCollateral_114b9705:Int +Int ( 1000000000000000000000000000000000000 *Int ( ( ( 1000000000000000000 *Int VV1_amountBorrowed_114b9705:Int ) +Int 799999999999999999 ) /Int 800000000000000000 ) ) ) +Int -1 )

    claim [zero-ge-left]:
      <k> runLemma (
        0 >=Int ( ( VV2_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV1_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) /Int 1000000000000000000000000000000000000 )
      ) => doneLemma (
        ( VV2_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV1_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) <Int 1000000000000000000000000000000000000
      ) ... </k>
    requires 100 <=Int VV1_amountBorrowed_114b9705:Int
       andBool 10000000000 <=Int VV2_priceCollateral_114b9705:Int
       andBool VV1_amountBorrowed_114b9705:Int <=Int 10000000000000000000000000000
       andBool VV2_priceCollateral_114b9705:Int <=Int 10000000000000000000000000000000000000000
       andBool ( pow128 *Int VV2_priceCollateral_114b9705:Int ) <=Int ( ( VV2_priceCollateral_114b9705:Int +Int ( 1000000000000000000000000000000000000 *Int ( ( ( 1000000000000000000 *Int VV1_amountBorrowed_114b9705:Int ) +Int 799999999999999999 ) /Int 800000000000000000 ) ) ) +Int -1 )


    claim [left-le-zero]:
      <k> runLemma (
        ( ( VV2_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV1_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) /Int 1000000000000000000000000000000000000 ) <=Int 0
      ) => doneLemma (
        ( VV2_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV1_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) <Int 1000000000000000000000000000000000000
      ) ... </k>
    requires 100 <=Int VV1_amountBorrowed_114b9705:Int
      andBool 10000000000 <=Int VV2_priceCollateral_114b9705:Int
      andBool VV1_amountBorrowed_114b9705:Int <=Int 10000000000000000000000000000
      andBool VV2_priceCollateral_114b9705:Int <=Int 10000000000000000000000000000000000000000
      andBool ( pow128 *Int VV2_priceCollateral_114b9705:Int ) <=Int ( ( VV2_priceCollateral_114b9705:Int +Int ( 1000000000000000000000000000000000000 *Int ( ( ( 1000000000000000000 *Int VV1_amountBorrowed_114b9705:Int ) +Int 799999999999999999 ) /Int 800000000000000000 ) ) ) +Int -1 )

    claim [pre-pre-chop]:
      <k> runLemma (
        ( pow128 *Int VV4_priceCollateral_114b9705:Int ) <=Int maxUInt256
      ) => doneLemma (
        VV4_priceCollateral_114b9705 <Int pow128
      ) ... </k>

    claim [pre-chop-1]:
      <k> runLemma (
        0 <=Int ( pow128 *Int ( maxUInt128 &Int ( ( 1000000 *Int ( ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) /Int 1000000000000000000000000000000000000 ) ) -Int ( ( ( ( 1000000 *Int ( ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) /Int 1000000000000000000000000000000000000 ) ) +Int 1000000 ) *Int VV3_amountRepaid_114b9705:Int ) /Int ( ( ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) /Int 1000000000000000000000000000000000000 ) +Int 1 ) ) ) ) )
      ) => doneLemma (
        true
      ) ... </k>
      requires 1 <=Int VV3_amountRepaid_114b9705:Int
       andBool 100 <=Int VV2_amountBorrowed_114b9705:Int
       andBool 10000000000 <=Int VV4_priceCollateral_114b9705:Int
       andBool VV2_amountBorrowed_114b9705:Int <=Int 10000000000000000000000000000
       andBool VV4_priceCollateral_114b9705:Int <Int pow128
       andBool 1000000000000000000000000000000000000 <=Int ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) )
       andBool ( 1000000000000000000000000000000000000 *Int VV3_amountRepaid_114b9705:Int ) <=Int ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) )
       andBool ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) <Int ( 1000000000000000000000000000000000000 *Int ( VV0_amountSupplied_114b9705:Int +Int 1 ) )
       andBool ( pow128 *Int VV4_priceCollateral_114b9705:Int ) <=Int ( ( VV4_priceCollateral_114b9705:Int +Int ( 1000000000000000000000000000000000000 *Int ( ( ( 1000000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) +Int 799999999999999999 ) /Int 800000000000000000 ) ) ) +Int -1 )

    claim [pre-chop-2]:
      <k> runLemma (
        ( pow128 *Int ( maxUInt128 &Int ( ( 1000000 *Int ( ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) /Int 1000000000000000000000000000000000000 ) ) -Int ( ( ( ( 1000000 *Int ( ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) /Int 1000000000000000000000000000000000000 ) ) +Int 1000000 ) *Int VV3_amountRepaid_114b9705:Int ) /Int ( ( ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) /Int 1000000000000000000000000000000000000 ) +Int 1 ) ) ) ) ) <Int pow256
      ) => doneLemma (
        true
      ) ... </k>
      requires 1 <=Int VV3_amountRepaid_114b9705:Int
       andBool 100 <=Int VV2_amountBorrowed_114b9705:Int
       andBool 10000000000 <=Int VV4_priceCollateral_114b9705:Int
       andBool VV2_amountBorrowed_114b9705:Int <=Int 10000000000000000000000000000
       andBool VV4_priceCollateral_114b9705:Int <Int pow128
       andBool 1000000000000000000000000000000000000 <=Int ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) )
       andBool ( 1000000000000000000000000000000000000 *Int VV3_amountRepaid_114b9705:Int ) <=Int ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) )
       andBool ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) <Int ( 1000000000000000000000000000000000000 *Int ( VV0_amountSupplied_114b9705:Int +Int 1 ) )
       andBool ( pow128 *Int VV4_priceCollateral_114b9705:Int ) <=Int ( ( VV4_priceCollateral_114b9705:Int +Int ( 1000000000000000000000000000000000000 *Int ( ( ( 1000000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) +Int 799999999999999999 ) /Int 800000000000000000 ) ) ) +Int -1 )

    claim [chop-chop]:
      <k> runLemma (
        ( chop ( ( pow128 *Int ( maxUInt128 &Int ( ( 1000000 *Int ( ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) /Int 1000000000000000000000000000000000000 ) ) -Int ( ( ( ( 1000000 *Int ( ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) /Int 1000000000000000000000000000000000000 ) ) +Int 1000000 ) *Int VV3_amountRepaid_114b9705:Int ) /Int ( ( ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) /Int 1000000000000000000000000000000000000 ) +Int 1 ) ) ) ) ) ) |Int ( ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) /Int 1000000000000000000000000000000000000 ) )
      ) => doneLemma (
        true
      ) ... </k>
      requires 1 <=Int VV3_amountRepaid_114b9705:Int
       andBool 100 <=Int VV2_amountBorrowed_114b9705:Int
       andBool 10000000000 <=Int VV4_priceCollateral_114b9705:Int
       andBool VV2_amountBorrowed_114b9705:Int <=Int 10000000000000000000000000000
       andBool VV4_priceCollateral_114b9705:Int <Int pow128
       andBool 1000000000000000000000000000000000000 <=Int ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) )
       andBool ( 1000000000000000000000000000000000000 *Int VV3_amountRepaid_114b9705:Int ) <=Int ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) )
       andBool ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) <Int ( 1000000000000000000000000000000000000 *Int ( VV0_amountSupplied_114b9705:Int +Int 1 ) )
       andBool ( pow128 *Int VV4_priceCollateral_114b9705:Int ) <=Int ( ( VV4_priceCollateral_114b9705:Int +Int ( 1000000000000000000000000000000000000 *Int ( ( ( 1000000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) +Int 799999999999999999 ) /Int 800000000000000000 ) ) ) +Int -1 )

    claim [zero-gt-expr]:
      <k> runLemma (
        0 <=Int ( ( 1000000 *Int ( ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) /Int 1000000000000000000000000000000000000 ) ) -Int ( ( ( ( 1000000 *Int ( ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) /Int 1000000000000000000000000000000000000 ) ) +Int 1000000 ) *Int VV3_amountRepaid_114b9705:Int ) /Int ( ( ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) /Int 1000000000000000000000000000000000000 ) +Int 1 ) ) )
      ) => doneLemma (
        true
      ) ... </k>
      requires 0 <=Int VV3_amountRepaid_114b9705:Int
       andBool 1 <=Int VV3_amountRepaid_114b9705:Int
       andBool 0 <=Int VV2_amountBorrowed_114b9705:Int
       andBool 0 <=Int VV4_priceCollateral_114b9705:Int
       andBool 100 <=Int VV2_amountBorrowed_114b9705:Int
       andBool 10000000000 <=Int VV4_priceCollateral_114b9705:Int
       andBool VV2_amountBorrowed_114b9705:Int <=Int 10000000000000000000000000000
       andBool VV4_priceCollateral_114b9705:Int <=Int 10000000000000000000000000000000000000000
       andBool VV3_amountRepaid_114b9705:Int <Int pow256
       andBool VV2_amountBorrowed_114b9705:Int <Int pow256
       andBool VV4_priceCollateral_114b9705:Int <Int pow256
       andBool ( maxUInt128 *Int VV4_priceCollateral_114b9705:Int ) <=Int maxUInt256
       andBool 1000000000000000000000000000000000000 <=Int ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) )
       andBool ( 1000000000000000000000000000000000000 *Int VV3_amountRepaid_114b9705:Int ) <=Int ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) )
       andBool ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) <Int ( 1000000000000000000000000000000000000 *Int ( VV0_amountSupplied_114b9705:Int +Int 1 ) )
       andBool ( pow128 *Int VV4_priceCollateral_114b9705:Int ) <=Int ( ( VV4_priceCollateral_114b9705:Int +Int ( 1000000000000000000000000000000000000 *Int ( ( ( 10 *Int VV2_amountBorrowed_114b9705:Int ) +Int 7 ) /Int 8 ) ) ) +Int -1 )

    claim [expr-lt-pow128]:
      <k> runLemma (
        ( ( 1000000 *Int ( ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) /Int 1000000000000000000000000000000000000 ) ) -Int ( ( ( ( 1000000 *Int ( ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) /Int 1000000000000000000000000000000000000 ) ) +Int 1000000 ) *Int VV3_amountRepaid_114b9705:Int ) /Int ( ( ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) /Int 1000000000000000000000000000000000000 ) +Int 1 ) ) ) <Int pow128
      ) => doneLemma (
        true
      ) ... </k>
      requires 0 <=Int VV3_amountRepaid_114b9705:Int
       andBool 1 <=Int VV3_amountRepaid_114b9705:Int
       andBool 0 <=Int VV2_amountBorrowed_114b9705:Int
       andBool 0 <=Int VV4_priceCollateral_114b9705:Int
       andBool 100 <=Int VV2_amountBorrowed_114b9705:Int
       andBool 10000000000 <=Int VV4_priceCollateral_114b9705:Int
       andBool VV2_amountBorrowed_114b9705:Int <=Int 10000000000000000000000000000
       andBool VV4_priceCollateral_114b9705:Int <=Int 10000000000000000000000000000000000000000
       andBool VV3_amountRepaid_114b9705:Int <Int pow256
       andBool VV2_amountBorrowed_114b9705:Int <Int pow256
       andBool VV4_priceCollateral_114b9705:Int <Int pow256
       andBool ( maxUInt128 *Int VV4_priceCollateral_114b9705:Int ) <=Int maxUInt256
       andBool 1000000000000000000000000000000000000 <=Int ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) )
       andBool ( 1000000000000000000000000000000000000 *Int VV3_amountRepaid_114b9705:Int ) <=Int ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) )
       andBool ( VV4_priceCollateral_114b9705:Int *Int ( ( 800000000000000000 *Int VV2_amountBorrowed_114b9705:Int ) /Int 1000000000000000000 ) ) <Int ( 1000000000000000000000000000000000000 *Int ( VV0_amountSupplied_114b9705:Int +Int 1 ) )
       andBool ( pow128 *Int VV4_priceCollateral_114b9705:Int ) <=Int ( ( VV4_priceCollateral_114b9705:Int +Int ( 1000000000000000000000000000000000000 *Int ( ( ( 10 *Int VV2_amountBorrowed_114b9705:Int ) +Int 7 ) /Int 8 ) ) ) +Int -1 )

    claim [gfob-pow128]:
      <k> runLemma (
        #getFirstOneBit(notMaxUInt128)
      ) => doneLemma (
        128
      ) ... </k>

endmodule