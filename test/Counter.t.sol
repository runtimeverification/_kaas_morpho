// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test, console} from "forge-std/Test.sol";
import {Counter} from "../src/Counter.sol";
import {KontrolCheats} from "kontrol-cheatcodes/KontrolCheats.sol";

contract CounterTest is Test, KontrolCheats {
    Counter public counter;

    function setUp() public {
        counter = new Counter();
        counter.setNumber(0, false);
    }

    function testIncrement() public {
        counter.increment();
        assert(counter.number() == 1);
    }

    function prove_SetNumber(uint256 x, bool inLuck) public {
        kevm.symbolicStorage(address(counter));
        counter.setNumber(x, inLuck);
        assert(counter.number() == x);
    }
}