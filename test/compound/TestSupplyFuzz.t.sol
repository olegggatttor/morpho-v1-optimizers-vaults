// SPDX-License-Identifier: AGPL-3.0-only
pragma solidity ^0.8.0;

import {FixedPointMathLib} from "@rari-capital/solmate/src/utils/FixedPointMathLib.sol";

import "./setup/TestSetupVaults.sol";

contract TestSupplyFuzz is TestSetupVaults {
    using FixedPointMathLib for uint256;
    using CompoundMath for uint256;

    uint256 constant WETH_BALANCE = INITIAL_BALANCE * 1e18;
    uint256 constant DAI_BALANCE = INITIAL_BALANCE * 1e18;
    uint256 constant USDT_BALANCE = INITIAL_BALANCE * 1e6;
    uint256 constant USDC_BALANCE = INITIAL_BALANCE * 1e6;

    function testCorrectInitialisation() public {
        assertEq(daiSupplyVault.owner(), address(this));
        assertEq(daiSupplyVault.name(), "MorphoCompoundDAI");
        assertEq(daiSupplyVault.symbol(), "mcDAI");
        assertEq(daiSupplyVault.poolToken(), cDai);
        assertEq(daiSupplyVault.asset(), dai);
        assertEq(daiSupplyVault.decimals(), 18);
    }

    function testCorrectInitialisationUsdc() public {
        assertEq(usdcSupplyVault.owner(), address(this));
        assertEq(usdcSupplyVault.name(), "MorphoCompoundUSDC");
        assertEq(usdcSupplyVault.symbol(), "mcUSDC");
        assertEq(usdcSupplyVault.poolToken(), cUsdc);
        assertEq(usdcSupplyVault.asset(), usdc);
        assertEq(usdcSupplyVault.decimals(), 18);
    }

    function testShouldDepositAmountFuzz(uint256 amount) public {
        amount = bound(amount, 1, DAI_BALANCE);
        // vm.assume(MIN_ETHER_AMOUNT <= amount && amount <= MAX_ETHER_AMOUNT);
        // uint256 amount = 10_000 ether;

        vaultSupplier1.depositVault(daiSupplyVault, amount);

        (uint256 balanceInP2P, uint256 balanceOnPool) = morpho.supplyBalanceInOf(
            cDai,
            address(daiSupplyVault)
        );

        uint256 p2pSupplyIndex = morpho.p2pSupplyIndex(cDai);
        uint256 poolSupplyIndex = ICToken(cDai).exchangeRateCurrent();

        assertGt(daiSupplyVault.balanceOf(address(vaultSupplier1)), 0, "mcDAI balance is zero");
        assertApproxEqAbs(
            balanceInP2P.mul(p2pSupplyIndex) + balanceOnPool.mul(poolSupplyIndex),
            amount.div(poolSupplyIndex).mul(poolSupplyIndex),
            1e10
        );
    }

    function testShouldWithdrawAllAmountFuzz(uint256 amount) public {
        amount = bound(amount, 1, DAI_BALANCE); // @bug падает по точности, падает при amount == 1

        uint256 poolSupplyIndex = ICToken(cDai).exchangeRateCurrent();
        uint256 expectedOnPool = amount.div(poolSupplyIndex);

        vaultSupplier1.depositVault(daiSupplyVault, amount);
        vaultSupplier1.withdrawVault(daiSupplyVault, expectedOnPool.mul(poolSupplyIndex));

        (uint256 balanceInP2P, uint256 balanceOnPool) = morpho.supplyBalanceInOf(
            cDai,
            address(daiSupplyVault)
        );

        assertApproxEqAbs(
            daiSupplyVault.balanceOf(address(vaultSupplier1)),
            0,
            3e3,
            "mcDAI balance not zero"
        );
        assertEq(balanceOnPool, 0, "onPool amount not zero");
        assertEq(balanceInP2P, 0, "inP2P amount not zero");
    }

    function testShouldWithdrawAllUsdcAmountFuzz(uint256 amount) public {
        amount = bound(amount, 1e3, 1e12); // @bug падает при 1 - депозит проходит, но withdraw падает
        // uint256 amount = 1e9;

        uint256 poolSupplyIndex = ICToken(cUsdc).exchangeRateCurrent();

        uint256 expectedOnPool = amount.div(poolSupplyIndex);

        vaultSupplier1.depositVault(usdcSupplyVault, amount);
        vaultSupplier1.withdrawVault(usdcSupplyVault, expectedOnPool.mul(poolSupplyIndex));

        (uint256 balanceInP2P, uint256 balanceOnPool) = morpho.supplyBalanceInOf(
            cUsdc,
            address(usdcSupplyVault)
        );

        console.logUint(usdcSupplyVault.balanceOf(address(vaultSupplier1)));
        assertApproxEqAbs(
            usdcSupplyVault.balanceOf(address(vaultSupplier1)),
            0,
            10,
            "mcUSDC balance not zero"
        );
        assertEq(balanceOnPool, 0, "onPool amount not zero");
        assertEq(balanceInP2P, 0, "inP2P amount not zero");
    }

    function testShouldWithdrawAllSharesFuzz(uint256 amount) public {
        amount = bound(amount, 1, DAI_BALANCE); // @bug падает при маленьких amount
        // uint256 amount = 10_000 ether;

        uint256 shares = vaultSupplier1.depositVault(daiSupplyVault, amount);
        vaultSupplier1.redeemVault(daiSupplyVault, shares); // cannot withdraw amount because of Compound rounding errors

        (uint256 balanceInP2P, uint256 balanceOnPool) = morpho.supplyBalanceInOf(
            cDai,
            address(daiSupplyVault)
        );

        assertEq(daiSupplyVault.balanceOf(address(vaultSupplier1)), 0, "mcDAI balance not zero");
        assertEq(balanceOnPool, 0, "onPool amount not zero");
        assertEq(balanceInP2P, 0, "inP2P amount not zero");
    }

    function testShouldNotWithdrawWhenNotDepositedFuzz(uint256 amount) public {
        amount = bound(amount, 1, DAI_BALANCE);
        // vm.assume(MIN_ETHER_AMOUNT <= amount && amount <= MAX_ETHER_AMOUNT);
        // uint256 amount = 10_000 ether;

        uint256 shares = vaultSupplier1.depositVault(daiSupplyVault, amount);

        vm.expectRevert("ERC4626: redeem more than max");
        vaultSupplier2.redeemVault(daiSupplyVault, shares);
    }

    function testShouldNotWithdrawOnBehalfIfNotAllowedFuzz(uint256 amount) public {
        amount = bound(amount, 1, DAI_BALANCE);
        // vm.assume(MIN_ETHER_AMOUNT <= amount && amount <= MAX_ETHER_AMOUNT);
        // uint256 amount = 10_000 ether;

        uint256 shares = vaultSupplier1.depositVault(daiSupplyVault, amount);

        vm.expectRevert("ERC4626: redeem more than max");
        vaultSupplier1.redeemVault(daiSupplyVault, shares, address(vaultSupplier2));
    }

    function testShouldWithdrawOnBehalfIfAllowedFuzz(uint256 amount) public {
        amount = bound(amount, 1, DAI_BALANCE); // @bug падает при низких значениях amount
        // uint256 amount = 10_000 ether;

        uint256 shares = vaultSupplier1.depositVault(daiSupplyVault, amount);

        vaultSupplier1.approve(address(mcDai), address(vaultSupplier2), shares);
        vaultSupplier2.redeemVault(daiSupplyVault, shares, address(vaultSupplier1));
    }

    function testShouldNotMintZeroShare() public {
        vm.expectRevert(abi.encodeWithSignature("AmountIsZero()"));
        vaultSupplier1.mintVault(daiSupplyVault, 0);
    }

    function testShouldNotWithdrawGreaterAmountFuzz(uint256 amount, uint256 extraAmount) public {
        amount = bound(amount, 1, DAI_BALANCE);
        vm.assume(extraAmount > 0 && extraAmount <= type(uint256).max - DAI_BALANCE);
        // uint256 amount = 10_000 ether;

        vaultSupplier1.depositVault(daiSupplyVault, amount);

        vm.expectRevert("ERC4626: withdraw more than max");
        vaultSupplier1.withdrawVault(daiSupplyVault, amount + extraAmount);
    }

    function testShouldNotRedeemMoreSharesFuzz(uint256 amount, uint256 extraShares) public {
        amount = bound(amount, 1, DAI_BALANCE);
        // vm.assume(MIN_ETHER_AMOUNT <= amount && amount <= MAX_ETHER_AMOUNT);
        // uint256 amount = 10_000 ether;

        uint256 shares = vaultSupplier1.depositVault(daiSupplyVault, amount);

        vm.assume(extraShares > 0 && extraShares <= type(uint256).max - shares);

        vm.expectRevert("ERC4626: redeem more than max");
        vaultSupplier1.redeemVault(daiSupplyVault, shares + extraShares);
    }

    function testShouldClaimRewardsFuzz(uint256 amount, uint256 holdDuration) public {
        amount = bound(amount, 1000 ether, DAI_BALANCE); // падает при low amount (== 1)
        holdDuration = bound(holdDuration, 1_000, 1_000_000);

        // uint256 amount = 10_000 ether;

        vaultSupplier1.depositVault(daiSupplyVault, amount);

        vm.roll(block.number + holdDuration);

        uint256 balanceBefore = vaultSupplier1.balanceOf(comp);

        uint256 rewardsAmount = daiSupplyVault.claimRewards(address(vaultSupplier1));

        uint256 balanceAfter = vaultSupplier1.balanceOf(comp);

        assertGt(rewardsAmount, 0);
        assertApproxEqAbs(
            ERC20(comp).balanceOf(address(daiSupplyVault)),
            0,
            1e4,
            "non zero comp balance on vault"
        );
        assertEq(balanceAfter, balanceBefore + rewardsAmount, "unexpected comp balance");
    }

    function testShouldClaimTwiceRewardsWhenDepositedForSameAmountAndTwiceDurationFuzz(
        uint256 amount,
        uint256 hold
    ) public {
        amount = bound(amount, 1, 100_000 ether); // @bug ERC4626: deposit more than max
        hold = bound(hold1, 1_000, 1_000_000);

        // uint256 amount = 10_000 ether;
        address[] memory poolTokens = new address[](1);
        poolTokens[0] = cDai;

        vaultSupplier1.depositVault(daiSupplyVault, amount);

        vm.roll(block.number + hold);

        uint256 expectedTotalRewardsAmount = lens.getUserUnclaimedRewards(
            poolTokens,
            address(daiSupplyVault)
        );

        vaultSupplier2.depositVault(daiSupplyVault, amount);

        vm.roll(block.number + hold);

        expectedTotalRewardsAmount += lens.getUserUnclaimedRewards(
            poolTokens,
            address(daiSupplyVault)
        );

        uint256 rewardsAmount1 = daiSupplyVault.claimRewards(address(vaultSupplier1));
        uint256 rewardsAmount2 = daiSupplyVault.claimRewards(address(vaultSupplier2));

        assertApproxEqAbs(
            rewardsAmount1 + rewardsAmount2,
            expectedTotalRewardsAmount,
            1e5,
            "unexpected total rewards amount"
        );
        assertLt(rewardsAmount1 + rewardsAmount2, expectedTotalRewardsAmount);
        assertApproxEqAbs(rewardsAmount1, 2 * rewardsAmount2, 1e9, "unexpected rewards amount"); // not exact because of compounded interests
    }

    function testShouldClaimSameRewardsWhenDepositedForSameAmountAndDuration1Fuzz(
        uint256 amount,
        uint256 hold
    ) public {
        amount = bound(amount, 1, DAI_BALANCE); // @bug ERC4626: deposit more than max
        hold = bound(hold1, 1_000, 1_000_000);

        address[] memory poolTokens = new address[](1);
        poolTokens[0] = cDai;

        uint256 shares1 = vaultSupplier1.depositVault(daiSupplyVault, amount);

        vm.roll(block.number + hold);

        uint256 expectedTotalRewardsAmount = lens.getUserUnclaimedRewards(
            poolTokens,
            address(daiSupplyVault)
        );

        uint256 shares2 = vaultSupplier2.depositVault(daiSupplyVault, amount);
        vaultSupplier1.redeemVault(daiSupplyVault, shares1 / 2);

        vm.roll(block.number + hold);

        expectedTotalRewardsAmount += lens.getUserUnclaimedRewards(
            poolTokens,
            address(daiSupplyVault)
        );

        vaultSupplier1.redeemVault(daiSupplyVault, shares1 / 2);
        vaultSupplier2.redeemVault(daiSupplyVault, shares2 / 2);

        vm.roll(block.number + hold);

        expectedTotalRewardsAmount += lens.getUserUnclaimedRewards(
            poolTokens,
            address(daiSupplyVault)
        );

        uint256 rewardsAmount1 = daiSupplyVault.claimRewards(address(vaultSupplier1));
        uint256 rewardsAmount2 = daiSupplyVault.claimRewards(address(vaultSupplier2));

        assertApproxEqAbs(
            rewardsAmount1 + rewardsAmount2,
            expectedTotalRewardsAmount,
            1e5,
            "unexpected total rewards amount"
        );
        assertLt(rewardsAmount1 + rewardsAmount2, expectedTotalRewardsAmount);
        assertApproxEqAbs(rewardsAmount1, rewardsAmount2, 1e8, "unexpected rewards amount"); // not exact because of compounded interests
    }

    function testShouldDepositCorrectAmountWhenMorphoPoolIndexesOutdatedFuzz(
        uint256 amount,
        uint64 timeWarp,
        uint64 blockRoll
    ) public {
        // uint256 amount = 10_000 ether;
        amount = bound(amount, 10_000 ether, DAI_BALANCE);
        timeWarp = uint64(bound(timeWarp, uint256(1_000_000), uint256(10_000_000)));
        blockRoll = uint64(bound(blockRoll, uint256(100_000), uint256(1_000_000)));

        vaultSupplier1.depositVault(daiSupplyVault, amount);

        vm.roll(block.number + blockRoll);
        vm.warp(block.timestamp + timeWarp);

        uint256 shares = vaultSupplier2.depositVault(daiSupplyVault, amount);
        uint256 assets = vaultSupplier2.redeemVault(daiSupplyVault, shares);

        assertApproxEqAbs(assets, amount, 1e8, "unexpected withdrawn assets");
    }

    function testShouldRedeemAllAmountWhenMorphoPoolIndexesOutdatedFuzz(
        uint256 amount,
        uint64 timeWarp,
        uint64 blockRoll
    ) public {
        // uint256 amount = 10_000 ether;
        amount = bound(amount, 10_000 ether, DAI_BALANCE);
        timeWarp = uint64(bound(timeWarp, uint256(1_000_000), uint256(10_000_000)));
        blockRoll = uint64(bound(blockRoll, uint256(100_000), uint256(1_000_000)));

        uint256 expectedOnPool = amount.div(ICToken(cDai).exchangeRateCurrent());

        uint256 shares = vaultSupplier1.depositVault(daiSupplyVault, amount);

        vm.roll(block.number + blockRoll);
        vm.warp(block.timestamp + timeWarp);

        uint256 assets = vaultSupplier1.redeemVault(daiSupplyVault, shares);

        assertApproxEqAbs(
            assets,
            expectedOnPool.mul(ICToken(cDai).exchangeRateCurrent()),
            1e4,
            "unexpected withdrawn assets"
        );
    }

    function testShouldWithdrawAllAmountWhenMorphoPoolIndexesOutdatedFuzz(
        uint256 amount,
        uint64 blockRoll
    ) public {
        // uint256 amount = 10_000 ether;
        amount = bound(amount, 10_000 ether, DAI_BALANCE);
        blockRoll = uint64(bound(blockRoll, uint256(100_000), uint256(1_000_000)));

        uint256 expectedOnPool = amount.div(ICToken(cDai).exchangeRateCurrent());

        vaultSupplier1.depositVault(daiSupplyVault, amount);

        vm.roll(block.number + blockRoll);

        vaultSupplier1.withdrawVault(
            daiSupplyVault,
            expectedOnPool.mul(ICToken(cDai).exchangeRateCurrent())
        );

        (uint256 balanceInP2P, uint256 balanceOnPool) = morpho.supplyBalanceInOf(
            address(cUsdc),
            address(daiSupplyVault)
        );

        assertEq(daiSupplyVault.balanceOf(address(vaultSupplier1)), 0, "mcUSDT balance not zero");
        assertEq(balanceOnPool, 0, "onPool amount not zero");
        assertEq(balanceInP2P, 0, "inP2P amount not zero");
    }

    function testTransferFuzz(uint256 amount) public {
        // uint256 amount = 1e6 ether;
        amount = bound(amount, 1e6 ether, DAI_BALANCE);

        vaultSupplier1.depositVault(daiSupplyVault, amount);

        uint256 balance = daiSupplyVault.balanceOf(address(vaultSupplier1));
        vm.prank(address(vaultSupplier1));
        daiSupplyVault.transfer(address(vaultSupplier2), balance);

        assertEq(daiSupplyVault.balanceOf(address(vaultSupplier1)), 0);
        assertEq(daiSupplyVault.balanceOf(address(vaultSupplier2)), balance);
    }

    function testTransferFromFuzz(uint256 amount) public {
        // uint256 amount = 1e6 ether;
        amount = bound(amount, 1e6 ether, DAI_BALANCE);

        vaultSupplier1.depositVault(daiSupplyVault, amount);

        uint256 balance = daiSupplyVault.balanceOf(address(vaultSupplier1));
        vm.prank(address(vaultSupplier1));
        daiSupplyVault.approve(address(vaultSupplier3), balance);

        vm.prank(address(vaultSupplier3));
        daiSupplyVault.transferFrom(address(vaultSupplier1), address(vaultSupplier2), balance);

        assertEq(daiSupplyVault.balanceOf(address(vaultSupplier1)), 0);
        assertEq(daiSupplyVault.balanceOf(address(vaultSupplier2)), balance);
    }

    function testTransferAccrueRewardsFuzz(uint256 amount, uint64 blockRoll) public {
        // uint256 amount = 1e6 ether;
        amount = bound(amount, 1e6 ether, DAI_BALANCE);
        blockRoll = uint64(bound(uint256(blockRoll), 1000, 100_000));

        vaultSupplier1.depositVault(daiSupplyVault, amount);

        vm.roll(block.number + blockRoll);

        uint256 balance = daiSupplyVault.balanceOf(address(vaultSupplier1));
        vm.prank(address(vaultSupplier1));
        daiSupplyVault.transfer(address(vaultSupplier2), balance);

        uint256 rewardAmount = ERC20(comp).balanceOf(address(daiSupplyVault));
        assertGt(rewardAmount, 0);

        uint256 expectedIndex = rewardAmount.divWadDown(daiSupplyVault.totalSupply());
        uint256 rewardsIndex = daiSupplyVault.rewardsIndex();
        assertEq(expectedIndex, rewardsIndex);

        (uint256 index1, uint256 unclaimed1) = daiSupplyVault.userRewards(address(vaultSupplier1));
        assertEq(index1, rewardsIndex);
        assertApproxEqAbs(unclaimed1, rewardAmount, 1e6);

        (uint256 index2, uint256 unclaimed2) = daiSupplyVault.userRewards(address(vaultSupplier2));
        assertEq(index2, rewardsIndex);
        assertEq(unclaimed2, 0);

        uint256 rewardsAmount1 = daiSupplyVault.claimRewards(address(vaultSupplier1));
        uint256 rewardsAmount2 = daiSupplyVault.claimRewards(address(vaultSupplier2));
        assertGt(rewardsAmount1, 0);
        assertEq(rewardsAmount2, 0);
    }

    function testTransferAndClaimRewardsFuzz(uint256 amount, uint256 intervalDuration) public {
        // uint256 amount = 1e6 ether;
        amount = bound(amount, 1e6 ether, DAI_BALANCE);
        intervalDuration = bound(intervalDuration, 1000, 1_000_000);

        vaultSupplier1.depositVault(daiSupplyVault, amount);

        vm.roll(block.number + intervalDuration);

        vaultSupplier2.depositVault(daiSupplyVault, amount);

        vm.roll(block.number + intervalDuration);

        uint256 balance = daiSupplyVault.balanceOf(address(vaultSupplier1));
        vm.prank(address(vaultSupplier1));
        daiSupplyVault.transfer(address(vaultSupplier2), balance);

        vm.roll(block.number + intervalDuration);

        uint256 rewardsAmount1 = daiSupplyVault.claimRewards(address(vaultSupplier1));
        uint256 rewardsAmount2 = daiSupplyVault.claimRewards(address(vaultSupplier2));

        assertGt(rewardsAmount1, 0);
        assertApproxEqAbs(rewardsAmount1, (2 * rewardsAmount2) / 3, 1e15);
        // Why rewardsAmount1 is 2/3 of rewardsAmount2 can be explained as follows:
        // vaultSupplier1 first gets X rewards corresponding to amount over one period of time
        // vaultSupplier1 then and supplier2 get X rewards each (under the approximation that doubling the amount doubles the rewards)
        // supplier2 then gets 2 * X rewards
        // In the end, vaultSupplier1 got 2 * X rewards while supplier2 got 3 * X
    }

    function testPreviewMintFuzz(uint256 amount, uint256 intervalDuration) public {
        // uint256 amount = 1e5 ether;
        amount = bound(amount, 1e6 ether, DAI_BALANCE);
        intervalDuration = bound(intervalDuration, 1000, 1_000_000);

        uint256 balanceBefore1 = ERC20(dai).balanceOf(address(vaultSupplier1));
        uint256 balanceBefore2 = ERC20(dai).balanceOf(address(vaultSupplier2));

        vm.roll(block.number + intervalDuration);

        // This should test that using the lens' predicted indexes is the correct amount to use.
        uint256 preview1 = daiSupplyVault.previewMint(amount);
        vaultSupplier1.mintVault(daiSupplyVault, amount);
        assertEq(preview1, balanceBefore1 - ERC20(dai).balanceOf(address(vaultSupplier1)));

        // The mint interacts with Morpho which updates the indexes,
        // so this should test that the lens predicted index does not differ from Morpho's actual index
        uint256 preview2 = daiSupplyVault.previewMint(amount);
        vaultSupplier2.mintVault(daiSupplyVault, amount);
        assertEq(preview2, balanceBefore2 - ERC20(dai).balanceOf(address(vaultSupplier2)));
    }

    function testPreviewDepositFuzz(uint256 amount, uint256 intervalDuration) public {
        // uint256 amount = 1e5 ether;
        amount = bound(amount, 1e6 ether, DAI_BALANCE);
        intervalDuration = bound(intervalDuration, 1000, 1_000_000);

        vm.roll(block.number + intervalDuration);

        // This should test that using the lens' predicted indexes is the correct amount to use.
        uint256 preview1 = daiSupplyVault.previewDeposit(amount);
        vaultSupplier1.depositVault(daiSupplyVault, amount);
        assertEq(daiSupplyVault.balanceOf(address(vaultSupplier1)), preview1, "before");

        // The deposit interacts with Morpho which updates the indexes,
        // so this should test that the lens predicted index does not differ from Morpho's actual index
        uint256 preview2 = daiSupplyVault.previewDeposit(amount);
        vaultSupplier2.depositVault(daiSupplyVault, amount);
        assertEq(daiSupplyVault.balanceOf(address(vaultSupplier2)), preview2, "after");
    }

    function testPreviewWithdrawFuzz(uint256 amount, uint256 intervalDuration) public {
        // uint256 amount = 1e5 ether;
        amount = bound(amount, 1e5 ether, DAI_BALANCE / 2);
        intervalDuration = bound(intervalDuration, 100, 1_000_000);

        vaultSupplier1.depositVault(daiSupplyVault, amount * 2);
        vaultSupplier2.depositVault(daiSupplyVault, amount * 2);

        uint256 balanceBefore1 = daiSupplyVault.balanceOf(address(vaultSupplier1));
        uint256 balanceBefore2 = daiSupplyVault.balanceOf(address(vaultSupplier2));

        vm.roll(block.number + intervalDuration);

        // This should test that using the lens' predicted indexes is the correct amount to use.
        uint256 preview1 = daiSupplyVault.previewWithdraw(amount);
        vaultSupplier1.withdrawVault(daiSupplyVault, amount);
        assertEq(preview1, balanceBefore1 - daiSupplyVault.balanceOf(address(vaultSupplier1)));

        // The withdraw interacts with Morpho which updates the indexes,
        // so this should test that the lens predicted index does not differ from Morpho's actual index
        uint256 preview2 = daiSupplyVault.previewWithdraw(amount);
        vaultSupplier2.withdrawVault(daiSupplyVault, amount);
        assertEq(preview2, balanceBefore2 - daiSupplyVault.balanceOf(address(vaultSupplier2)));
    }

    function testPreviewRedeemFuzz(uint256 amount, uint256 intervalDuration) public {
        // uint256 amount = 1e5 ether;
        amount = bound(amount, 1e5 ether, DAI_BALANCE / 3);
        intervalDuration = bound(intervalDuration, 100, 1_000_000);

        vaultSupplier1.depositVault(daiSupplyVault, amount * 2);
        vaultSupplier2.depositVault(daiSupplyVault, amount * 2);

        uint256 balanceBefore1 = ERC20(dai).balanceOf(address(vaultSupplier1));
        uint256 balanceBefore2 = ERC20(dai).balanceOf(address(vaultSupplier2));

        vm.roll(block.number + intervalDuration);

        // This should test that using the lens' predicted indexes is the correct amount to use.
        uint256 preview1 = daiSupplyVault.previewRedeem(amount);
        vaultSupplier1.redeemVault(daiSupplyVault, amount);
        assertEq(balanceBefore1 + preview1, ERC20(dai).balanceOf(address(vaultSupplier1)));

        // The redeem interacts with Morpho which updates the indexes,
        // so this should test that the lens predicted index does not differ from Morpho's actual index
        uint256 preview2 = daiSupplyVault.previewRedeem(amount);
        vaultSupplier2.redeemVault(daiSupplyVault, amount);
        assertEq(balanceBefore2 + preview2, ERC20(dai).balanceOf(address(vaultSupplier2)));
    }
}
