/* 
*  Invariants in CVL are proved by structural induction on the contract
*  Base Case: Constructor
*  Step Case: any method of the contract
*  We assume the invariant before the execution of one step, and prove it still holds after, i.e. the invariant is inductive. 
*  Preserved{} Blocks: The proof of some invariants might depend on others. To this end, we use the preserved{} block requiring all other invariants. This is logically sound given that each invariant is proved. For simplicity of the spec, we simply require all invariants if at least one is needed. 
*/

function allInvariants(){
    requireInvariant validatorUniqueness();
    requireInvariant validatorNotZero();
    requireInvariant zeroNotValidator();
    requireInvariant validatorIsValid();
    requireInvariant zeroAddressInValidatorsZero();
    requireInvariant transactionUniqueness();
    requireInvariant transactionIdIsValid();
    requireInvariant quorumIsValid();
    requireInvariant zeroInTransactionIdsLength();
    requireInvariant validatorsInitializedToZero();
    requireInvariant transactionIdsReverseMapValidity();
    requireInvariant zeroBytesNotValidTransactionId();
    requireInvariant zeroBytesInTransactionIdsZero();
    requireInvariant zeroBytesInTransactionIdsReverseMapZero();
    requireInvariant lengthIsNotZero();
    requireInvariant validatorsReverseMapValid();
    requireInvariant validatorsReverseMapUniqeness();
    requireInvariant validatorsReverseMapStoresCorrectIndex();
    requireInvariant validatorsReverseMapValidIndex();
    requireInvariant canPayRewardsPot();
    requireInvariant validatorNotThis();
    requireInvariant thisNotValidator();
    requireInvariant validatorHasReverseLookup();
    requireInvariant validatorsRemovalTickNotInTheFuture();
    requireInvariant transactionsTickNotInFuture();
    requireInvariant transactionExist_IFF_notInFuture();
    requireInvariant confirmationsTickNotInFuture();
    requireInvariant transactionsRemovalTickNotInFuture();
    requireInvariant transactionsRemovalTickCorelationTransactionsTick();
    requireInvariant confirmationsTickNotAfterRemoval();
    requireInvariant tickNotZero();
    requireInvariant thisCannotBeCreator();
    require currentContract.transactionIds.length != max_uint256;
}


/* ############ VALIDATOR INVARIANTS ############## */

invariant zeroNotValidator()
    !currentContract.isValidator[0];

invariant thisNotValidator()
    !currentContract.isValidator[currentContract];

invariant validatorUniqueness()
    forall uint256 i. forall uint256 j. (j < currentContract.validators.length && i < j) 
        => currentContract.validators[i] != currentContract.validators[j] 
    {
        preserved {
            allInvariants();
        }
    }

invariant validatorHasReverseLookup()
    forall address a. currentContract.validatorsReverseMap[a] != 0 <=> currentContract.isValidator[a]
    {
        preserved {
            allInvariants();
        }
    }

invariant validatorNotZero()
    forall uint256 i. (i != 0 && i < currentContract.validators.length) <=> currentContract.validators[i] != 0
    {
        preserved {
            allInvariants();
        }
    }

invariant validatorNotThis()
    forall uint256 i. (i < currentContract.validators.length) => currentContract.validators[i] != currentContract
    {
        preserved {
            allInvariants();
        }
    }

invariant validatorsInitializedToZero()
    forall uint256 i. i >= currentContract.validators.length => currentContract.validators[i] == 0
    {
        preserved {
            allInvariants();
        }
    }

invariant zeroAddressInValidatorsZero()
    currentContract.validators[0] == 0
    {
        preserved {
            allInvariants();
        }
    }

invariant lengthIsNotZero()
    (currentContract.validators.length != 0) && (currentContract.transactionIds.length != 0)
    {
        preserved {
            allInvariants();
        }
    }


invariant validatorIsValid()
    forall uint256 i. (i != 0 && i < currentContract.validators.length) <=> currentContract.isValidator[currentContract.validators[i]]
    {
        preserved {
            allInvariants();
        }
    }

invariant validatorsReverseMapValid()
    forall uint256 i. (i < currentContract.validators.length => currentContract.validatorsReverseMap[currentContract.validators[i]] == i)
    {
        preserved {
            allInvariants();
        }
    }

invariant validatorsReverseMapValidIndex()
    forall address a. currentContract.validatorsReverseMap[a] < currentContract.validators.length
    {
        preserved {
            allInvariants();
        }
    }

invariant validatorsReverseMapStoresCorrectIndex()
    forall address a. currentContract.validatorsReverseMap[a] != 0 
        => currentContract.validators[currentContract.validatorsReverseMap[a]] == a
    {
        preserved {
            allInvariants();
        }
    }

invariant validatorsReverseMapUniqeness()
    forall address a. forall address b. 
        (
            a != b 
            && currentContract.validatorsReverseMap[a] != 0 
            && currentContract.validatorsReverseMap[b] != 0
        ) 
        => currentContract.validatorsReverseMap[a] != currentContract.validatorsReverseMap[b]
    {
        preserved {
            allInvariants();
        }
    }

/* ############ TRANSACTION INVARIANTS ############## */

invariant thisCannotBeCreator()
    forall bytes32 transactionId. currentContract.transactions[transactionId].creator != currentContract;

invariant transactionUniqueness()
    forall uint256 i. forall uint256 j. (j < currentContract.transactionIds.length && i < j) 
    => currentContract.transactionIds[i] != currentContract.transactionIds[j]
    {
        preserved {
            allInvariants();
        }
    }

invariant zeroBytesInTransactionIdsZero()
    currentContract.transactionIds[0] == to_bytes32(0)
    {
        preserved {
            allInvariants();
        }
    }

invariant zeroBytesInTransactionIdsReverseMapZero()
    currentContract.transactionIdsReverseMap[to_bytes32(0)] == 0
    {
        preserved {
            allInvariants();
        }
    }

invariant zeroBytesNotValidTransactionId()
    forall uint256 i. (i != 0 && i < currentContract.transactionIds.length) => (currentContract.transactionIds[i] != to_bytes32(0))
    {
        preserved {
            allInvariants();
        }
    }

invariant transactionIdsReverseMapValidity()
    (forall uint256 i. 
        i < currentContract.transactionIds.length => currentContract.transactionIdsReverseMap[currentContract.transactionIds[i]] == i)
    && (forall bytes32 id. 
        ((currentContract.transactionIdsReverseMap[id] != 0) => (currentContract.transactionIds[currentContract.transactionIdsReverseMap[id]] == id)) && (currentContract.transactionIdsReverseMap[id] < currentContract.transactionIds.length))
    && (forall bytes32 id. 
        currentContract.transactionIdsReverseMap[id] != 0 <=> (currentContract.transactions[id].destination != 0))
    {
        preserved {
            allInvariants();
        }
    }

invariant zeroInTransactionIdsLength()
    forall uint256 i. i >= currentContract.transactionIds.length => currentContract.transactionIds[i] == to_bytes32(0)
    {
        preserved {
            allInvariants();
        }
    }

invariant transactionIdIsValid()
    forall uint256 i. (i != 0 && i < currentContract.transactionIds.length) <=> currentContract.transactions[currentContract.transactionIds[i]].destination != 0
    {
        preserved {
            allInvariants();
        }
    }

invariant emptyTransactionIsEmpty(bytes32 transactionId)
    currentContract.transactions[transactionId].destination == 0 => 
    (getConfirmationCount(transactionId) == 0 &&
    (currentContract.transactions[transactionId].value == 0 && 
    getDataOfTransaction(transactionId).length == 0 && 
    currentContract.transactions[transactionId].hasReward == false && 
    currentContract.transactions[transactionId].executed == false &&
    currentContract.transactions[transactionId].creator == 0))
    {
        preserved {
            allInvariants();
        }
    }

/* ############ TICK INVARIANTS ############## */

invariant tickNotZero()
    currentContract.tick != 0;

invariant validatorsRemovalTickNotInTheFuture()
    forall address a. (currentContract.validatorsRemovalTick[a] < currentContract.tick);

invariant transactionsTickNotInFuture()
    forall bytes32 transactionId. currentContract.transactionsTick[transactionId] < currentContract.tick;

invariant transactionExist_IFF_notInFuture()
    forall bytes32 transactionId. currentContract.transactions[transactionId].destination == 0 <=> currentContract.transactionsTick[transactionId] == 0;

invariant confirmationsTickNotInFuture()
    forall address a. forall bytes32 transactionId. a != 0 
        => currentContract.confirmationsTick[transactionId][a] < currentContract.tick;

invariant confirmationsTickNotAfterRemoval()
    forall address a. forall bytes32 transactionId. (!currentContract.isValidator[a]) => (currentContract.confirmationsTick[transactionId][a] <= currentContract.validatorsRemovalTick[a])
    {
        preserved {
            allInvariants();
        }
    }

invariant transactionsRemovalTickNotInFuture()
    forall bytes32 transactionId. currentContract.transactionsRemovalTick[transactionId] < currentContract.tick;

invariant transactionsRemovalTickCorelationTransactionsTick()
    forall bytes32 transactionId. currentContract.transactionsRemovalTick[transactionId] != 0 => 
    ((currentContract.transactionsRemovalTick[transactionId] != currentContract.transactionsTick[transactionId]) && 
    (currentContract.transactions[transactionId].destination != 0 => currentContract.transactionsRemovalTick[transactionId] < currentContract.transactionsTick[transactionId]));

/* ############ OTHER INVARIANTS ############## */

invariant canPayRewardsPot()
    nativeBalances[currentContract] >= currentContract.confirmedRewardsPot + currentContract.pendingRewardsPot + currentContract.transactionsTotalValue;

invariant quorumIsValid()
    currentContract.quorum <= currentContract.validators.length && currentContract.quorum != 0;