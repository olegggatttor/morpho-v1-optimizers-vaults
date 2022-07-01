// SPDX-License-Identifier: GNU AGPLv3
pragma solidity ^0.8.0;

import "./setup/TestSetupVaults.sol";

contract TestSupplyHarvestVault is TestSetupVaults {
    using CompoundMath for uint256;

    function testShouldDepositAmount() public {
        uint256 amount = 10000 ether;

        vaultSupplier1.depositVault(daiSupplyHarvestVault, amount);

        (uint256 balanceInP2P, uint256 balanceOnPool) = morpho.supplyBalanceInOf(
            cDai,
            address(daiSupplyHarvestVault)
        );

        uint256 p2pSupplyIndex = morpho.p2pSupplyIndex(cDai);
        uint256 poolSupplyIndex = ICToken(cDai).exchangeRateCurrent();

        assertGt(
            daiSupplyHarvestVault.balanceOf(address(vaultSupplier1)),
            0,
            "mchDAI balance is zero"
        );
        assertApproxEqAbs(
            balanceInP2P.mul(p2pSupplyIndex) + balanceOnPool.mul(poolSupplyIndex),
            amount.div(poolSupplyIndex).mul(poolSupplyIndex),
            1e10
        );
    }

    function testShouldWithdrawAllAmount() public {
        uint256 amount = 10000 ether;

        uint256 poolSupplyIndex = ICToken(cDai).exchangeRateCurrent();
        uint256 expectedOnPool = amount.div(poolSupplyIndex);

        vaultSupplier1.depositVault(daiSupplyHarvestVault, amount);
        vaultSupplier1.withdrawVault(daiSupplyHarvestVault, expectedOnPool.mul(poolSupplyIndex));

        (uint256 balanceInP2P, uint256 balanceOnPool) = morpho.supplyBalanceInOf(
            cDai,
            address(daiSupplyHarvestVault)
        );

        assertApproxEqAbs(
            daiSupplyHarvestVault.balanceOf(address(vaultSupplier1)),
            0,
            1e3,
            "mcDAI balance not zero"
        );
        assertEq(balanceOnPool, 0, "onPool amount not zero");
        assertEq(balanceInP2P, 0, "inP2P amount not zero");
    }

    function testShouldWithdrawAllUsdcAmount() public {
        uint256 amount = 1e9;

        uint256 poolSupplyIndex = ICToken(cUsdc).exchangeRateCurrent();
        uint256 expectedOnPool = amount.div(poolSupplyIndex);

        vaultSupplier1.depositVault(usdcSupplyHarvestVault, amount);
        vaultSupplier1.withdrawVault(usdcSupplyHarvestVault, expectedOnPool.mul(poolSupplyIndex));

        (uint256 balanceInP2P, uint256 balanceOnPool) = morpho.supplyBalanceInOf(
            cUsdc,
            address(usdcSupplyHarvestVault)
        );

        assertEq(
            usdcSupplyHarvestVault.balanceOf(address(vaultSupplier1)),
            0,
            "mcUSDC balance not zero"
        );
        assertEq(balanceOnPool, 0, "onPool amount not zero");
        assertEq(balanceInP2P, 0, "inP2P amount not zero");
    }

    function testShouldWithdrawAllShares() public {
        uint256 amount = 10000 ether;

        uint256 shares = vaultSupplier1.depositVault(daiSupplyHarvestVault, amount);
        vaultSupplier1.redeemVault(daiSupplyHarvestVault, shares); // cannot withdraw amount because of Compound rounding errors

        (uint256 balanceInP2P, uint256 balanceOnPool) = morpho.supplyBalanceInOf(
            cDai,
            address(daiSupplyHarvestVault)
        );

        assertEq(
            daiSupplyHarvestVault.balanceOf(address(vaultSupplier1)),
            0,
            "mcDAI balance not zero"
        );
        assertEq(balanceOnPool, 0, "onPool amount not zero");
        assertEq(balanceInP2P, 0, "inP2P amount not zero");
    }

    function testShouldNotWithdrawWhenNotDeposited() public {
        uint256 amount = 10000 ether;

        uint256 shares = vaultSupplier1.depositVault(daiSupplyHarvestVault, amount);

        vm.expectRevert("ERC4626: redeem more than max");
        vaultSupplier2.redeemVault(daiSupplyHarvestVault, shares);
    }

    function testShouldNotWithdrawOnBehalfIfNotAllowed() public {
        uint256 amount = 10000 ether;

        uint256 shares = vaultSupplier1.depositVault(daiSupplyHarvestVault, amount);

        vm.expectRevert("ERC4626: redeem more than max");
        vaultSupplier1.redeemVault(daiSupplyHarvestVault, shares, address(vaultSupplier2));
    }

    function testShouldWithdrawOnBehalfIfAllowed() public {
        uint256 amount = 10000 ether;

        uint256 shares = vaultSupplier1.depositVault(daiSupplyHarvestVault, amount);

        vaultSupplier1.approve(address(mchDai), address(vaultSupplier2), shares);
        vaultSupplier2.redeemVault(daiSupplyHarvestVault, shares, address(vaultSupplier1));
    }

    function testShouldNotMintZeroShare() public {
        vm.expectRevert(abi.encodeWithSignature("AmountIsZero()"));
        vaultSupplier1.mintVault(daiSupplyHarvestVault, 0);
    }

    function testShouldNotWithdrawGreaterAmount() public {
        uint256 amount = 10000 ether;

        vaultSupplier1.depositVault(daiSupplyHarvestVault, amount);

        vm.expectRevert("ERC4626: withdraw more than max");
        vaultSupplier1.withdrawVault(daiSupplyHarvestVault, amount * 2);
    }

    function testShouldNotRedeemMoreShares() public {
        uint256 amount = 10000 ether;

        uint256 shares = vaultSupplier1.depositVault(daiSupplyHarvestVault, amount);

        vm.expectRevert("ERC4626: redeem more than max");
        vaultSupplier1.redeemVault(daiSupplyHarvestVault, shares + 1);
    }

    function testShouldClaimAndFoldRewards() public {
        uint256 amount = 10_000 ether;

        vaultSupplier1.depositVault(daiSupplyHarvestVault, amount);

        vm.roll(block.number + 1_000);

        morpho.updateP2PIndexes(cDai);
        (, uint256 balanceOnPoolBefore) = morpho.supplyBalanceInOf(
            cDai,
            address(daiSupplyHarvestVault)
        );

        (uint256 rewardsAmount, uint256 rewardsFee) = daiSupplyHarvestVault.harvest(
            daiSupplyHarvestVault.maxHarvestingSlippage()
        );
        uint256 expectedRewardsFee = ((rewardsAmount + rewardsFee) *
            daiSupplyHarvestVault.harvestingFee()) / daiSupplyHarvestVault.MAX_BASIS_POINTS();

        (, uint256 balanceOnPoolAfter) = morpho.supplyBalanceInOf(
            cDai,
            address(daiSupplyHarvestVault)
        );

        assertGt(rewardsAmount, 0, "rewards amount is zero");
        assertEq(
            balanceOnPoolAfter,
            balanceOnPoolBefore + rewardsAmount.div(ICToken(cDai).exchangeRateCurrent()),
            "unexpected balance on pool"
        );
        assertEq(
            ERC20(comp).balanceOf(address(daiSupplyHarvestVault)),
            0,
            "comp amount is not zero"
        );
        assertEq(rewardsFee, expectedRewardsFee, "unexpected rewards fee amount");
        assertEq(ERC20(dai).balanceOf(address(this)), rewardsFee, "unexpected fee collected");
    }

    function testShouldClaimAndRedeemRewards() public {
        uint256 amount = 10_000 ether;

        uint256 shares = vaultSupplier1.depositVault(daiSupplyHarvestVault, amount);

        vm.roll(block.number + 1_000);

        morpho.updateP2PIndexes(cDai);
        (, uint256 balanceOnPoolBefore) = morpho.supplyBalanceInOf(
            cDai,
            address(daiSupplyHarvestVault)
        );
        uint256 balanceBefore = vaultSupplier1.balanceOf(dai);

        (uint256 rewardsAmount, uint256 rewardsFee) = daiSupplyHarvestVault.harvest(
            daiSupplyHarvestVault.maxHarvestingSlippage()
        );
        uint256 expectedRewardsFee = ((rewardsAmount + rewardsFee) *
            daiSupplyHarvestVault.harvestingFee()) / daiSupplyHarvestVault.MAX_BASIS_POINTS();

        vaultSupplier1.redeemVault(daiSupplyHarvestVault, shares);
        uint256 balanceAfter = vaultSupplier1.balanceOf(dai);

        assertEq(
            ERC20(dai).balanceOf(address(daiSupplyHarvestVault)),
            0,
            "non zero dai balance on vault"
        );
        assertGt(
            balanceAfter,
            balanceBefore + balanceOnPoolBefore + rewardsAmount,
            "unexpected dai balance"
        );
        assertEq(rewardsFee, expectedRewardsFee, "unexpected rewards fee amount");
        assertEq(ERC20(dai).balanceOf(address(this)), rewardsFee, "unexpected fee collected");
    }

    function testShouldNotAllowOracleDumpManipulation() public {
        uint256 amount = 10_000 ether;

        vaultSupplier1.depositVault(daiSupplyHarvestVault, amount);

        vm.roll(block.number + 1_000);

        uint256 flashloanAmount = 1_000 ether;
        ISwapRouter swapRouter = daiSupplyHarvestVault.SWAP_ROUTER();

        deal(comp, address(this), flashloanAmount);
        ERC20(comp).approve(address(swapRouter), flashloanAmount);
        swapRouter.exactInputSingle(
            ISwapRouter.ExactInputSingleParams({
                tokenIn: comp,
                tokenOut: wEth,
                fee: daiSupplyHarvestVault.compSwapFee(),
                recipient: address(this),
                deadline: block.timestamp,
                amountIn: flashloanAmount,
                amountOutMinimum: 0,
                sqrtPriceLimitX96: 0
            })
        );

        vm.expectRevert("Too little received");
        daiSupplyHarvestVault.harvest(100);
    }
}
