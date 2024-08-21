// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity ^0.8.0;

import "./BaseTest.k.sol";

contract KontrolRepayIntegrationTest is KontrolBaseTest {
    using MathLib for uint256;
    using MorphoLib for IMorpho;
    using SharesMathLib for uint256;

    function testRepayMarketNotCreated(MarketParams memory marketParamsFuzz) public {
        vm.assume(neq(marketParamsFuzz, marketParams));

        vm.expectRevert(bytes(ErrorsLib.MARKET_NOT_CREATED));
        morpho.repay(marketParamsFuzz, 1, 0, address(this), hex"");
    }

    function testRepayZeroAmount() public {
        vm.expectRevert(bytes(ErrorsLib.INCONSISTENT_INPUT));
        morpho.repay(marketParams, 0, 0, address(this), hex"");
    }

    function testRepayInconsistentInput(uint256 amount, uint256 shares) public {
        amount = bound(amount, 1, MAX_TEST_AMOUNT);
        shares = bound(shares, 1, MAX_TEST_SHARES);

        vm.expectRevert(bytes(ErrorsLib.INCONSISTENT_INPUT));
        morpho.repay(marketParams, amount, shares, address(this), hex"");
    }

    function testRepayOnBehalfZeroAddress(uint256 input, bool isAmount) public {
        input = bound(input, 1, type(uint256).max);
        vm.expectRevert(bytes(ErrorsLib.ZERO_ADDRESS));
        morpho.repay(marketParams, isAmount ? input : 0, isAmount ? 0 : input, address(0), hex"");
    }

    function testBHPMinimum(
      uint256 amountCollateral,
      uint256 amountBorrowed,
      uint256 priceCollateral
    ) public returns (uint256){
        priceCollateral = bound(priceCollateral, MIN_COLLATERAL_PRICE, MAX_COLLATERAL_PRICE);
        amountBorrowed = bound(amountBorrowed, MIN_TEST_AMOUNT, MAX_TEST_AMOUNT);

        uint256 minCollateral = amountBorrowed.wDivUp(marketParams.lltv).mulDivUp(ORACLE_PRICE_SCALE, priceCollateral);

        if (minCollateral <= MAX_COLLATERAL_ASSETS) {
            amountCollateral = bound(amountCollateral, minCollateral, MAX_COLLATERAL_ASSETS);
        } else {
            amountCollateral = MAX_COLLATERAL_ASSETS;
            uint256 left = amountBorrowed.wMulDown(marketParams.lltv).mulDivDown(priceCollateral, ORACLE_PRICE_SCALE);
            uint256 right = MAX_TEST_AMOUNT;
            assertTrue(left < right);
            amountBorrowed = left;
        }

        vm.assume(amountBorrowed > 0);
        return amountBorrowed;
    }

    function testBHPMinimumModel(
      uint256 amountCollateral,
      uint256 amountBorrowed,
      uint256 priceCollateral
    ) public returns (uint256) {
        priceCollateral = 10000000000;
        amountBorrowed = 2722258935368;

        uint256 left;
        uint256 right = MAX_TEST_AMOUNT;

        uint256 minCollateral = amountBorrowed.wDivUp(marketParams.lltv).mulDivUp(ORACLE_PRICE_SCALE, priceCollateral);

        if (minCollateral <= MAX_COLLATERAL_ASSETS) {
            assertTrue(false);
        } else {
            amountCollateral = MAX_COLLATERAL_ASSETS;
            left = amountBorrowed.wMulDown(marketParams.lltv).mulDivDown(priceCollateral, ORACLE_PRICE_SCALE);
            assertTrue(left < right);
        }

        return left;
    }

    function testRepayAssets(
        uint256 amountSupplied,
        uint256 amountCollateral,
        uint256 amountBorrowed,
        uint256 amountRepaid,
        uint256 priceCollateral
    ) public {
        (amountCollateral, amountBorrowed, priceCollateral) =
            _boundHealthyPosition(amountCollateral, amountBorrowed, priceCollateral);
        return;

        amountSupplied = bound(amountSupplied, amountBorrowed, MAX_TEST_AMOUNT);
        _supply(amountSupplied);

        oracle.setPrice(priceCollateral);

        amountRepaid = bound(amountRepaid, 1, amountBorrowed);
        uint256 expectedBorrowShares = amountBorrowed.toSharesUp(0, 0);
        uint256 expectedRepaidShares = amountRepaid.toSharesDown(amountBorrowed, expectedBorrowShares);

        collateralToken.setBalance(ONBEHALF, amountCollateral);
        loanToken.setBalance(REPAYER, amountRepaid);

        vm.startPrank(ONBEHALF);
        morpho.supplyCollateral(marketParams, amountCollateral, ONBEHALF, hex"");
        morpho.borrow(marketParams, amountBorrowed, 0, ONBEHALF, RECEIVER);
        vm.stopPrank();

        vm.startPrank(REPAYER);
        vm.expectEmit(true, true, true, true, address(morpho));
        emit EventsLib.Repay(id, REPAYER, ONBEHALF, amountRepaid, expectedRepaidShares);
        (uint256 returnAssets, uint256 returnShares) = morpho.repay(marketParams, amountRepaid, 0, ONBEHALF, hex"");
        vm.stopPrank();

        expectedBorrowShares -= expectedRepaidShares;

        assertEq(returnAssets, amountRepaid, "returned asset amount");
        assertEq(returnShares, expectedRepaidShares, "returned shares amount");
        assertEq(morpho.borrowShares(id, ONBEHALF), expectedBorrowShares, "borrow shares");
        assertEq(morpho.totalBorrowAssets(id), amountBorrowed - amountRepaid, "total borrow");
        assertEq(morpho.totalBorrowShares(id), expectedBorrowShares, "total borrow shares");
        assertEq(loanToken.balanceOf(RECEIVER), amountBorrowed, "RECEIVER balance");
        assertEq(loanToken.balanceOf(address(morpho)), amountSupplied - amountBorrowed + amountRepaid, "morpho balance");
    }

    function testRepayShares(
        uint256 amountSupplied,
        uint256 amountCollateral,
        uint256 amountBorrowed,
        uint256 sharesRepaid,
        uint256 priceCollateral
    ) public {
        (amountCollateral, amountBorrowed, priceCollateral) =
            _boundHealthyPosition(amountCollateral, amountBorrowed, priceCollateral);

        amountSupplied = bound(amountSupplied, amountBorrowed, MAX_TEST_AMOUNT);
        _supply(amountSupplied);

        oracle.setPrice(priceCollateral);

        uint256 expectedBorrowShares = amountBorrowed.toSharesUp(0, 0);
        sharesRepaid = bound(sharesRepaid, 1, expectedBorrowShares);
        uint256 expectedAmountRepaid = sharesRepaid.toAssetsUp(amountBorrowed, expectedBorrowShares);

        collateralToken.setBalance(ONBEHALF, amountCollateral);
        loanToken.setBalance(REPAYER, expectedAmountRepaid);

        vm.startPrank(ONBEHALF);
        morpho.supplyCollateral(marketParams, amountCollateral, ONBEHALF, hex"");
        morpho.borrow(marketParams, amountBorrowed, 0, ONBEHALF, RECEIVER);
        vm.stopPrank();

        vm.prank(REPAYER);

        vm.expectEmit(true, true, true, true, address(morpho));
        emit EventsLib.Repay(id, REPAYER, ONBEHALF, expectedAmountRepaid, sharesRepaid);
        (uint256 returnAssets, uint256 returnShares) = morpho.repay(marketParams, 0, sharesRepaid, ONBEHALF, hex"");

        expectedBorrowShares -= sharesRepaid;

        assertEq(returnAssets, expectedAmountRepaid, "returned asset amount");
        assertEq(returnShares, sharesRepaid, "returned shares amount");
        assertEq(morpho.borrowShares(id, ONBEHALF), expectedBorrowShares, "borrow shares");
        assertEq(morpho.totalBorrowAssets(id), amountBorrowed - expectedAmountRepaid, "total borrow");
        assertEq(morpho.totalBorrowShares(id), expectedBorrowShares, "total borrow shares");
        assertEq(loanToken.balanceOf(RECEIVER), amountBorrowed, "RECEIVER balance");
        assertEq(
            loanToken.balanceOf(address(morpho)),
            amountSupplied - amountBorrowed + expectedAmountRepaid,
            "morpho balance"
        );
    }

    function testRepayMax(uint256 shares) public {
        shares = bound(shares, MIN_TEST_SHARES, MAX_TEST_SHARES);

        uint256 assets = shares.toAssetsUp(0, 0);

        loanToken.setBalance(address(this), assets);

        morpho.supply(marketParams, 0, shares, SUPPLIER, hex"");

        collateralToken.setBalance(address(this), HIGH_COLLATERAL_AMOUNT);

        morpho.supplyCollateral(marketParams, HIGH_COLLATERAL_AMOUNT, BORROWER, hex"");

        vm.prank(BORROWER);
        morpho.borrow(marketParams, 0, shares, BORROWER, RECEIVER);

        loanToken.setBalance(address(this), assets);

        morpho.repay(marketParams, 0, shares, BORROWER, hex"");
    }
}
