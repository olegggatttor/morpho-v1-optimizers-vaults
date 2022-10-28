// SPDX-License-Identifier: GNU AGPLv3
pragma solidity 0.8.13;

import {IAToken} from "@contracts/aave-v2/interfaces/aave/IAToken.sol";
import {IMorpho} from "@contracts/aave-v2/interfaces/IMorpho.sol";

import {OwnableUpgradeable} from "@openzeppelin/contracts-upgradeable/access/OwnableUpgradeable.sol";
import {ERC20, SafeTransferLib} from "@rari-capital/solmate/src/utils/SafeTransferLib.sol";
import {WadRayMath} from "@morpho-labs/morpho-utils/math/WadRayMath.sol";
import {Math} from "@morpho-labs/morpho-utils/math/Math.sol";
import {Types} from "@contracts/aave-v2/libraries/Types.sol";

import {ERC4626UpgradeableSafe, ERC20Upgradeable} from "../ERC4626UpgradeableSafe.sol";

/// @title SupplyVaultBase.
/// @author Morpho Labs.
/// @custom:contact security@morpho.xyz
/// @notice ERC4626-upgradeable Tokenized Vault abstract implementation for Morpho-Aave V2.
abstract contract SupplyVaultBase is ERC4626UpgradeableSafe, OwnableUpgradeable {
    using WadRayMath for uint256;
    using SafeTransferLib for ERC20;

    /// EVENTS ///

    /// @notice Emitted when MORPHO rewards are transferred to `recipient`.
    /// @param recipient The recipient of the rewards.
    event RewardsRecipientSet(address recipient);

    /// @notice Emitted when rewards rewards are transferred to `recipient`.
    /// @param recipient The recipient of the rewards.
    /// @param amount The amount of rewards transferred.
    event RewardsTransferred(address recipient, uint256 amount);

    /// ERRORS ///

    /// @notice Thrown when the zero address is passed as input or is the recipient address when calling `transferRewards`.
    error ZeroAddress();

    /// CONSTANTS AND IMMUTABLES ///

    IMorpho public immutable morpho; // The main Morpho contract.
    ERC20 public immutable morphoToken; // The address of the Morpho Token.

    /// STORAGE ///

    address public poolToken; // The pool token corresponding to the market to supply to through this vault.
    address public recipient; // The recipient of the rewards that will redistribute them to vault's users.

    /// CONSTRUCTOR ///

    /// @dev Initializes network-wide immutables.
    /// @param _morpho The address of the main Morpho contract.
    /// @param _morphoToken The address of the Morpho Token.
    constructor(address _morpho, address _morphoToken) {
        if (_morpho == address(0) || _morphoToken == address(0)) revert ZeroAddress();
        morpho = IMorpho(_morpho);
        morphoToken = ERC20(_morphoToken);
    }

    /// INITIALIZER ///

    /// @dev Initializes the vault.
    /// @param _poolToken The address of the pool token corresponding to the market to supply through this vault.
    /// @param _name The name of the ERC20 token associated to this tokenized vault.
    /// @param _symbol The symbol of the ERC20 token associated to this tokenized vault.
    /// @param _initialDeposit The amount of the initial deposit used to prevent pricePerShare manipulation.
    function __SupplyVaultBase_init(
        address _poolToken,
        string calldata _name,
        string calldata _symbol,
        uint256 _initialDeposit
    ) internal onlyInitializing {
        ERC20 underlyingToken = __SupplyVaultBase_init_unchained(_poolToken);

        __Ownable_init_unchained();
        __ERC20_init_unchained(_name, _symbol);
        __ERC4626_init_unchained(ERC20Upgradeable(address(underlyingToken)));
        __ERC4626UpgradeableSafe_init_unchained(_initialDeposit);
    }

    /// @dev Initializes the vault whithout initializing parent contracts (avoid the double initialization problem).
    /// @param _poolToken The address of the pool token corresponding to the market to supply through this vault.
    function __SupplyVaultBase_init_unchained(address _poolToken)
        internal
        onlyInitializing
        returns (ERC20 underlyingToken)
    {
        poolToken = _poolToken;

        underlyingToken = ERC20(IAToken(_poolToken).UNDERLYING_ASSET_ADDRESS()); // Reverts on zero address so no check for pool token needed.
        underlyingToken.safeApprove(address(morpho), type(uint256).max);
    }

    /// EXTERNAL ///

    /// @notice Sets the rewards recipient.
    /// @param _recipient The new rewards recipient.
    function setRewardsRecipient(address _recipient) external onlyOwner {
        if (_recipient == address(0)) revert ZeroAddress();
        recipient = _recipient;
        emit RewardsRecipientSet(_recipient);
    }

    /// @notice Transfers the MORPHO rewards to the rewards recipient.
    /// @dev Anybody can trigger this function. This offloads the DAO to do it.
    function transferRewards() external {
        if (recipient == address(0)) revert ZeroAddress();
        uint256 amount = morphoToken.balanceOf(address(this));
        morphoToken.safeTransfer(recipient, amount);
        emit RewardsTransferred(recipient, amount);
    }

    /// PUBLIC ///

    /// @dev The indexes used by this function might not be up-to-date.
    ///      As a consequence, view functions (like `maxWithdraw`) could underestimate the withdrawable amount.
    ///      To redeem all their assets, users are encouraged to use the `redeem` function passing their vault tokens balance.
    function totalAssets() public view virtual override returns (uint256) {
        address poolTokenMem = poolToken;
        Types.SupplyBalance memory supplyBalance = morpho.supplyBalanceInOf(
            poolTokenMem,
            address(this)
        );

        return
            supplyBalance.onPool.rayMul(morpho.poolIndexes(poolTokenMem).poolSupplyIndex) +
            supplyBalance.inP2P.rayMul(morpho.p2pSupplyIndex(poolTokenMem));
    }

    function deposit(uint256 assets, address receiver) public virtual override returns (uint256) {
        // Update the indexes to get the most up-to-date total assets balance.
        morpho.updateIndexes(poolToken);
        return super.deposit(assets, receiver);
    }

    function mint(uint256 shares, address receiver) public virtual override returns (uint256) {
        // Update the indexes to get the most up-to-date total assets balance.
        morpho.updateIndexes(poolToken);
        return super.mint(shares, receiver);
    }

    function withdraw(
        uint256 assets,
        address receiver,
        address owner
    ) public virtual override returns (uint256) {
        // Update the indexes to get the most up-to-date total assets balance.
        morpho.updateIndexes(poolToken);
        return super.withdraw(assets, receiver, owner);
    }

    function redeem(
        uint256 shares,
        address receiver,
        address owner
    ) public virtual override returns (uint256) {
        // Update the indexes to get the most up-to-date total assets balance.
        morpho.updateIndexes(poolToken);
        return super.redeem(shares, receiver, owner);
    }

    /// INTERNAL ///

    function _deposit(
        address _caller,
        address _receiver,
        uint256 _assets,
        uint256 _shares
    ) internal virtual override {
        super._deposit(_caller, _receiver, _assets, _shares);
        morpho.supply(address(poolToken), address(this), _assets);
    }

    function _withdraw(
        address _caller,
        address _receiver,
        address _owner,
        uint256 _assets,
        uint256 _shares
    ) internal virtual override {
        morpho.withdraw(address(poolToken), _assets);
        super._withdraw(_caller, _receiver, _owner, _assets, _shares);
    }

    /// @dev This empty reserved space is put in place to allow future versions to add new
    /// variables without shifting down storage in the inheritance chain.
    /// See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
    uint256[48] private __gap;
}
