-include .env.local
.EXPORT_ALL_VARIABLES:

PROTOCOL?=compound
NETWORK?=eth-mainnet

FOUNDRY_SRC=src/${PROTOCOL}/
FOUNDRY_TEST=test/${PROTOCOL}/
FOUNDRY_REMAPPINGS=@config/=lib/morpho-contracts/config/${NETWORK}/${PROTOCOL}/
FOUNDRY_ETH_RPC_URL?=https://rpc.ankr.com/eth

ifeq (${NETWORK}, eth-mainnet)
  FOUNDRY_CHAIN_ID=1
  FOUNDRY_FORK_BLOCK_NUMBER=15425110
endif

ifeq (${NETWORK}, polygon-mainnet)
  FOUNDRY_CHAIN_ID=137
  FOUNDRY_FORK_BLOCK_NUMBER=22116728
endif

ifeq (${NETWORK}, avalanche-mainnet)
  FOUNDRY_CHAIN_ID=43114
  FOUNDRY_ETH_RPC_URL=https://api.avax.network/ext/bc/C/rpc
  FOUNDRY_FORK_BLOCK_NUMBER=12675271
endif


install:
	@yarn
	@foundryup
	@git submodule update --init --recursive

build:
	@forge build --sizes --force

test-deploy:
	@echo Building transactions to deploy vaults for Morpho-${PROTOCOL} on \"${NETWORK}\"
	@forge script scripts/${PROTOCOL}/${NETWORK}/Deploy.s.sol:Deploy -vvv

deploy:
	@echo Deploying vaults for Morpho-${PROTOCOL} on \"${NETWORK}\"
	@forge script scripts/${PROTOCOL}/${NETWORK}/Deploy.s.sol:Deploy -vv --broadcast --private-key ${DEPLOYER_PRIVATE_KEY} --with-gas-price 40000000000

test:
	@echo Running all Morpho-${PROTOCOL} tests on \"${NETWORK}\" at block \"${FOUNDRY_FORK_BLOCK_NUMBER}\" with seed \"${FOUNDRY_FUZZ_SEED}\"
	@forge test --no-match-path **/live/** -vv | tee trace.ansi

live:
	@echo Running all Morpho-${PROTOCOL} tests on \"${NETWORK}\" at block \"${FOUNDRY_FORK_BLOCK_NUMBER}\" with seed \"${FOUNDRY_FUZZ_SEED}\"
	@forge test --match-path **/live/** -vvv | tee trace.ansi

gas-report:
	@echo Creating gas report for Morpho-${PROTOCOL} on \"${NETWORK}\" at block \"${FOUNDRY_FORK_BLOCK_NUMBER}\" with seed \"${FOUNDRY_FUZZ_SEED}\"
	@forge test --no-match-path **/live/** --gas-report

coverage:
	@echo Create lcov coverage report for Morpho-${PROTOCOL} tests on \"${NETWORK}\" at block \"${FOUNDRY_FORK_BLOCK_NUMBER}\" with seed \"${FOUNDRY_FUZZ_SEED}\"
	@forge coverage --report lcov

lcov-html:
	@echo Transforming the lcov coverage report into html
	@genhtml lcov.info -o coverage

contract-% c-%:
	@echo Running tests for contract $* of Morpho-${PROTOCOL} on \"${NETWORK}\" at block \"${FOUNDRY_FORK_BLOCK_NUMBER}\" with seed \"${FOUNDRY_FUZZ_SEED}\"
	@forge test -vv --no-match-path **/live/** --match-contract $* | tee trace.ansi

single-% s-%:
	@echo Running single test $* of Morpho-${PROTOCOL} on \"${NETWORK}\" at block \"${FOUNDRY_FORK_BLOCK_NUMBER}\" with seed \"${FOUNDRY_FUZZ_SEED}\"
	@forge test -vvv --match-test $* | tee trace.ansi

storage-layout-gen-%:
	@./scripts/storage-layout.sh generate snapshots/.storage-layout-${PROTOCOL} $*

storage-layout-check-%:
	@./scripts/storage-layout.sh check snapshots/.storage-layout-${PROTOCOL} $*

config:
	@forge config

halmos:
	@halmos -vvvv --contract TestSupplyVault --function testShouldDepositAmount

fuzz:
	forge test --no-match-path **/live/** --match-test "Fuzz" -vv

.PHONY: test config common foundry coverage
