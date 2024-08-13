// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test} from "forge-std/Test.sol";
import {Morpho} from "lib/morpho-blue/src/Morpho.sol";
import {ErrorsLib} from "lib/morpho-blue/src/libraries/ErrorsLib.sol";

// "./libraries/ErrorsLib.sol

contract MorphoTest is Test {
    Morpho public morpho;

    function setUp() public {
        vm.chainId(1);
        morpho = new Morpho(address(this));
    }

    function proveDeployWithAddressZero() public {
        vm.expectRevert(bytes(ErrorsLib.ZERO_ADDRESS));
        new Morpho(address(0));
    }

    function proveSetOwnerWhenNotOwner(address addressFuzz) public {
        vm.assume(addressFuzz != address(this));
        vm.assume(addressFuzz != address(vm));
        vm.assume(addressFuzz != address(morpho));

        vm.prank(addressFuzz);
        vm.expectRevert(bytes(ErrorsLib.NOT_OWNER));
        morpho.setOwner(addressFuzz);
    }
}
