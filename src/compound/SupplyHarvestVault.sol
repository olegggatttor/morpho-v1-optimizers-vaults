// SPDX-License-Identifier: GNU AGPLv3
pragma solidity ^0.8.0;

import "@uniswap/v3-periphery/contracts/interfaces/ISwapRouter.sol";

import "./SupplyVaultUpgradeable.sol";

/// @title SupplyHarvestVault.
/// @author Morpho Labs.
/// @custom:contact security@morpho.xyz
/// @notice ERC4626-upgradeable tokenized Vault implementation for Morpho-Compound, which can harvest accrued COMP rewards, swap them and re-supply them through Morpho-Compound.
contract SupplyHarvestVault is SupplyVaultUpgradeable {
    using SafeTransferLib for ERC20;
    using CompoundMath for uint256;

    /// EVENTS ///

    /// @notice Emitted when the fee for harvesting is set.
    /// @param newHarvestingFee The new harvesting fee.
    event HarvestingFeeSet(uint16 newHarvestingFee);

    /// @notice Emitted when the fee for swapping comp for WETH is set.
    /// @param newCompSwapFee The new comp swap fee (in UniswapV3 fee unit).
    event CompSwapFeeSet(uint16 newCompSwapFee);

    /// @notice Emitted when the fee for swapping WETH for the underlying asset is set.
    /// @param newAssetSwapFee The new asset swap fee (in UniswapV3 fee unit).
    event AssetSwapFeeSet(uint16 newAssetSwapFee);

    /// @notice Emitted when the maximum slippage for harvesting is set.
    /// @param newMaxHarvestingSlippage The new maximum slippage allowed when swapping rewards for the underlying token (in bps).
    event MaxHarvestingSlippageSet(uint16 newMaxHarvestingSlippage);

    /// ERRORS ///

    /// @notice Thrown when the input is above the maximum basis points value (100%).
    error ExceedsMaxBasisPoints();

    /// @notice Thrown when the input is above the maximum UniswapV3 pool fee value (100%).
    error ExceedsMaxUniswapV3Fee();

    /// STORAGE ///

    uint16 public constant MAX_BASIS_POINTS = 10_000; // 100% in basis points.
    uint24 public constant MAX_UNISWAP_FEE = 1_000_000; // 100% in UniswapV3 fee units.
    ISwapRouter public constant SWAP_ROUTER =
        ISwapRouter(0xE592427A0AEce92De3Edee1F18E0157C05861564); // The address of UniswapV3SwapRouter.

    address public cComp; // The address of cCOMP token.

    uint24 public compSwapFee; // The fee taken by the UniswapV3Pool for swapping COMP rewards for WETH (in UniswapV3 fee unit).
    uint24 public assetSwapFee; // The fee taken by the UniswapV3Pool for swapping WETH for the underlying asset (in UniswapV3 fee unit).
    uint16 public harvestingFee; // The fee taken by the claimer when harvesting the vault (in bps).
    uint16 public maxHarvestingSlippage; // The maximum slippage allowed when swapping rewards for the underlying asset (in bps).

    /// UPGRADE ///

    /// @notice Initializes the vault.
    /// @param _morphoAddress The address of the main Morpho contract.
    /// @param _poolTokenAddress The address of the pool token corresponding to the market to supply through this vault.
    /// @param _name The name of the ERC20 token associated to this tokenized vault.
    /// @param _symbol The symbol of the ERC20 token associated to this tokenized vault.
    /// @param _initialDeposit The amount of the initial deposit used to prevent pricePerShare manipulation.
    /// @param _compSwapFee The fee taken by the UniswapV3Pool for swapping COMP rewards for WETH (in UniswapV3 fee unit).
    /// @param _assetSwapFee The fee taken by the UniswapV3Pool for swapping WETH for the underlying asset (in UniswapV3 fee unit).
    /// @param _harvestingFee The fee taken by the claimer when harvesting the vault (in bps).
    /// @param _maxHarvestingSlippage The maximum slippage allowed when swapping rewards for the underlying asset (in bps).
    function initialize(
        address _morphoAddress,
        address _poolTokenAddress,
        string calldata _name,
        string calldata _symbol,
        uint256 _initialDeposit,
        uint24 _compSwapFee,
        uint24 _assetSwapFee,
        uint16 _harvestingFee,
        uint16 _maxHarvestingSlippage,
        address _cComp
    ) external initializer {
        __SupplyVault_init(_morphoAddress, _poolTokenAddress, _name, _symbol, _initialDeposit);

        compSwapFee = _compSwapFee;
        assetSwapFee = _assetSwapFee;
        harvestingFee = _harvestingFee;
        maxHarvestingSlippage = _maxHarvestingSlippage;

        cComp = _cComp;
    }

    /// GOVERNANCE ///

    /// @notice Sets the fee taken by the UniswapV3Pool for swapping COMP rewards for WETH.
    /// @param _newCompSwapFee The new comp swap fee (in UniswapV3 fee unit).
    function setCompSwapFee(uint16 _newCompSwapFee) external onlyOwner {
        if (_newCompSwapFee > MAX_UNISWAP_FEE) revert ExceedsMaxUniswapV3Fee();

        compSwapFee = _newCompSwapFee;
        emit CompSwapFeeSet(_newCompSwapFee);
    }

    /// @notice Sets the fee taken by the UniswapV3Pool for swapping WETH for the underlying asset.
    /// @param _newAssetSwapFee The new asset swap fee (in UniswapV3 fee unit).
    function setAssetSwapFee(uint16 _newAssetSwapFee) external onlyOwner {
        if (_newAssetSwapFee > MAX_UNISWAP_FEE) revert ExceedsMaxUniswapV3Fee();

        assetSwapFee = _newAssetSwapFee;
        emit AssetSwapFeeSet(_newAssetSwapFee);
    }

    /// @notice Sets the fee taken by the claimer from the total amount of COMP rewards when harvesting the vault.
    /// @param _newHarvestingFee The new harvesting fee (in bps).
    function setHarvestingFee(uint16 _newHarvestingFee) external onlyOwner {
        if (_newHarvestingFee > MAX_BASIS_POINTS) revert ExceedsMaxBasisPoints();

        harvestingFee = _newHarvestingFee;
        emit HarvestingFeeSet(_newHarvestingFee);
    }

    /// @notice Sets the maximum slippage allowed when swapping rewards for the underlying token.
    /// @param _newMaxHarvestingSlippage The new maximum slippage allowed when swapping rewards for the underlying token (in bps).
    function setMaxHarvestingSlippage(uint16 _newMaxHarvestingSlippage) external onlyOwner {
        if (_newMaxHarvestingSlippage > MAX_BASIS_POINTS) revert ExceedsMaxBasisPoints();

        maxHarvestingSlippage = _newMaxHarvestingSlippage;
        emit MaxHarvestingSlippageSet(_newMaxHarvestingSlippage);
    }

    /// EXTERNAL ///

    /// @notice Harvests the vault: claims rewards from the underlying pool, swaps them for the underlying asset and supply them through Morpho.
    /// @param _maxSlippage The maximum slippage allowed for the swap (in bps).
    /// @return claimedAmount The amount of rewards claimed, swapped then supplied through Morpho (in underlying).
    /// @return rewardsFee The amount of fees taken by the claimer (in underlying).
    function harvest(uint16 _maxSlippage)
        external
        returns (uint256 claimedAmount, uint256 rewardsFee)
    {
        address poolTokenAddress = address(poolToken);

        {
            address[] memory poolTokenAddresses = new address[](1);
            poolTokenAddresses[0] = poolTokenAddress;
            morpho.claimRewards(poolTokenAddresses, false);
        }

        uint256 amountOutMinimum;
        {
            claimedAmount = comp.balanceOf(address(this)); // TODO: remove this once upgrade deployed on mainnet

            ICompoundOracle oracle = ICompoundOracle(comptroller.oracle());
            amountOutMinimum = claimedAmount
            .mul(oracle.getUnderlyingPrice(cComp))
            .div(oracle.getUnderlyingPrice(poolTokenAddress))
            .mul(MAX_BASIS_POINTS - CompoundMath.min(_maxSlippage, maxHarvestingSlippage))
            .div(MAX_BASIS_POINTS);
        }

        comp.safeApprove(address(SWAP_ROUTER), claimedAmount);
        claimedAmount = SWAP_ROUTER.exactInput(
            ISwapRouter.ExactInputParams({
                path: isEth
                    ? abi.encodePacked(address(comp), compSwapFee, wEth)
                    : abi.encodePacked(
                        address(comp),
                        compSwapFee,
                        wEth,
                        assetSwapFee,
                        address(asset)
                    ),
                recipient: address(this),
                deadline: block.timestamp,
                amountIn: claimedAmount,
                amountOutMinimum: amountOutMinimum
            })
        );

        if (harvestingFee > 0) {
            rewardsFee = (claimedAmount * harvestingFee) / MAX_BASIS_POINTS;
            claimedAmount -= rewardsFee;
        }

        morpho.supply(poolTokenAddress, address(this), claimedAmount);

        if (rewardsFee > 0) asset.safeTransfer(msg.sender, rewardsFee);
    }
}
