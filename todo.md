# Outstanding work on the Dots and Boxes development

Items 1 to 6 are independent of each other. Items 7 to 11 form one block, gated
on item 1 and then on item 8.

1. **Prove `loony_degrees` from the board geometry.** `comp_from_closed` and
   `board_comp_from_closed` take the degree bound as a hypothesis. A box in a
   chain or a loop has exactly two of its four walls undrawn, so the bound
   follows from the position being loony. Items 2 and 3 depend on it.

2. **Prove the loop and chain classification correct.** `cyclicb` sorts
   extracted runs into loops and chains, and reports true on a two-box run. The
   grid dual is triangle-free and its cycles are even, so at length three or
   more the test is exact.

3. **State the decomposition's order-independence.** `comp_from_closed` gives
   that the run is the connected component of its start, so the extracted set
   does not depend on which box the walk began from.

4. **Unify the two decomposition paths.** `loops_of`, `chains_of` and
   `board_position` account for every open box only under `board_loony`;
   `schains_of` and `sboard_position` do so unconditionally.

5. **Port Allcock's Theorem 1.5 to `svalue`.** Theorem 1.4 is
   `svalue_gt4_iff`. The closed-form test for a value above two, which the
   controller consults before keeping control at a chain, has no capped
   counterpart.

6. **Give `sv` a native classification.** `sv_collapse_one` reduces the fold to
   a single `h1` index when a one-box chain is present. `sv` calls `v41` on the
   long part and inherits its five branches, and the case with two-box chains
   alone routes through `g`.

7. **Characterize when legal play reaches a loony board.** `board_loony` is
   decidable; the states satisfying it are not characterized.

8. **Prove that the loony phase of board play simulates `eg` and `eplay`.** An
   endgame turn is several board moves, so the correspondence is not move for
   move. Items 9 to 11 follow from it.

9. **Tie `eg` to `db_moves` and `db_play`.** `score_eg` relates `value` to a
   scoring game defined alongside it.

10. **Tie `eplay` turn counts to `turns`.** This carries the long chain rule
    from the board to the endgame; `eturns_components` states the count inside
    the play model.

11. **Relate `value` to `forces_margin` and `margin_best_exists`.** The board
    carries a margin theory and the endgame a value theory, with no theorem
    between them.
