// SPDX-License-Identifier: GNU AGPLv3
pragma solidity ^0.8.0;

import "@morpho-contracts/contracts/compound/interfaces/compound/ICompound.sol";
import "@morpho-contracts/contracts/compound/interfaces/IMorpho.sol";

import {ERC20, SafeTransferLib} from "@rari-capital/solmate/src/utils/SafeTransferLib.sol";

import "@vaults/ERC4626Upgradeable.sol";

contract User {
    using SafeTransferLib for ERC20;

    IMorpho internal morpho;
    IComptroller internal comptroller;

    constructor(IMorpho _morpho) {
        morpho = _morpho;
        comptroller = morpho.comptroller();
    }

    function balanceOf(ERC20 _token) external view returns (uint256) {
        return _token.balanceOf(address(this));
    }

    function approve(
        ERC20 _token,
        address _spender,
        uint256 _amount
    ) public {
        _token.safeApprove(_spender, _amount);
    }

    function approve(ERC20 _token, uint256 _amount) external {
        approve(_token, address(morpho), _amount);
    }

    function deposit(ERC4626Upgradeable tokenizedVault, uint256 _amount)
        external
        returns (uint256)
    {
        return tokenizedVault.deposit(_amount, address(this));
    }

    function mint(ERC4626Upgradeable tokenizedVault, uint256 _shares) external returns (uint256) {
        return tokenizedVault.mint(_shares, address(this));
    }

    function withdraw(
        ERC4626Upgradeable tokenizedVault,
        uint256 _amount,
        address _owner
    ) public returns (uint256) {
        return tokenizedVault.withdraw(_amount, address(this), _owner);
    }

    function withdraw(ERC4626Upgradeable tokenizedVault, uint256 _amount)
        external
        returns (uint256)
    {
        return withdraw(tokenizedVault, _amount, address(this));
    }

    function redeem(
        ERC4626Upgradeable tokenizedVault,
        uint256 _shares,
        address _owner
    ) public returns (uint256) {
        return tokenizedVault.redeem(_shares, address(this), _owner);
    }

    function redeem(ERC4626Upgradeable tokenizedVault, uint256 _shares) external returns (uint256) {
        return redeem(tokenizedVault, _shares, address(this));
    }
}
