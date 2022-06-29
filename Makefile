-include .env.local
.EXPORT_ALL_VARIABLES:

PROTOCOL?=compound
NETWORK?=eth-mainnet
CHAIN_ID?=1

FOUNDRY_ETH_RPC_URL?=https://${NETWORK}.g.alchemy.com/v2/${ALCHEMY_KEY}
FOUNDRY_FORK_BLOCK_NUMBER?=14292587

export FOUNDRY_REMAPPINGS?=@config/=lib/morpho-contracts/config/${NETWORK}/${PROTOCOL}/
export FOUNDRY_TEST=test/${PROTOCOL}

ifeq (${NETWORK}, polygon-mainnet)
	export FOUNDRY_FORK_BLOCK_NUMBER=22116728

  ifeq (${PROTOCOL}, aave-v3)
  	export FOUNDRY_FORK_BLOCK_NUMBER=29116728
  endif
endif

ifeq (${NETWORK}, avalanche-mainnet)
	export FOUNDRY_ETH_RPC_URL=https://api.avax.network/ext/bc/C/rpc
	export FOUNDRY_FORK_BLOCK_NUMBER=12675271

	ifeq (${PROTOCOL}, aave-v3)
		export FOUNDRY_FORK_BLOCK_NUMBER=15675271
	endif
endif

ifneq (, $(filter ${NETWORK}, ropsten rinkeby))
  FOUNDRY_ETH_RPC_URL=https://${NETWORK}.infura.io/v3/${INFURA_PROJECT_ID}
endif


install:
	@yarn
	@foundryup
	@git submodule update --init --recursive

	cd lib/morpho-contracts && git checkout dev && cd ../..

test:
	@echo Running all ${PROTOCOL} tests on ${NETWORK}
	@forge test -vv

test-ansi:
	@echo Running all ${PROTOCOL} tests on ${NETWORK}
	@forge test -vv > trace.ansi

test-html:
	@echo Running all ${PROTOCOL} tests on ${NETWORK}
	@forge test -vv | aha --black > trace.html

contract-% c-%:
	@echo Running tests for contract $* of ${PROTOCOL} on ${NETWORK}
	@forge test -vvv/$*.t.sol --match-contract $*

ansi-c-%:
	@echo Running tests for contract $* of ${PROTOCOL} on ${NETWORK}
	@forge test -vvv/$*.t.sol --match-contract $* > trace.ansi

html-c-%:
	@echo Running tests for contract $* of ${PROTOCOL} on ${NETWORK}
	@forge test -vvv/$*.t.sol --match-contract $* | aha --black > trace.html

single-% s-%:
	@echo Running single test $* of ${PROTOCOL} on ${NETWORK}
	@forge test -vvv --match-test $*

ansi-s-%:
	@echo Running single test $* of ${PROTOCOL} on ${NETWORK}
	@forge test -vvvvv --match-test $* > trace.ansi

html-s-%:
	@echo Running single test $* of ${PROTOCOL} on ${NETWORK}
	@forge test -vvvvv --match-test $* | aha --black > trace.html

config:
	@forge config


.PHONY: test config common foundry
