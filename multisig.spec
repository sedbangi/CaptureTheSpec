import "invariants.spec";
import "sanity.spec";

methods {
    function addValidator(address, uint256) external;
    function removeValidator(address, uint256) external;
    function replaceValidator(address, address) external;
    function changeQuorum(uint256) external;
    function distributeRewards() external;
    function getDataOfTransaction(bytes32) external returns (bytes memory) envfree;
    function confirmedRewardsPot() external returns(uint256) envfree;
    function pendingRewardsPot() external returns(uint256) envfree;
    function tick() external returns(uint256) envfree;
    function FEE() external returns(uint256) envfree;
    function transactionsTotalValue() external returns(uint256) envfree;
    function isConfirmed(bytes32) external returns (bool) envfree;
    function hash(bytes) external returns (bytes32) envfree;
    function getConfirmationCount(bytes32) external returns (uint256) envfree;
    function transactionExists(bytes32) external returns (bool) envfree;
    function removeTransaction(bytes32) external;
    function executeTransaction(bytes32) external envfree;
    function _._ external => DISPATCH [
        currentContract.addValidator(address, uint256),
        currentContract.removeValidator(address, uint256),
        currentContract.replaceValidator(address, address),
        currentContract.changeQuorum(uint256),
        currentContract.removeTransaction(bytes32)
    ] default NONDET;
}

// imported from "invariants.spec"
use invariant validatorUniqueness;
use invariant validatorNotZero;
use invariant zeroNotValidator;
use invariant validatorIsValid;
use invariant zeroAddressInValidatorsZero;
use invariant transactionUniqueness;
use invariant transactionIdIsValid;
use invariant quorumIsValid;
use invariant zeroInTransactionIdsLength;
use invariant validatorsInitializedToZero;
use invariant transactionIdsReverseMapValidity;
use invariant zeroBytesNotValidTransactionId;
use invariant zeroBytesInTransactionIdsZero;
use invariant zeroBytesInTransactionIdsReverseMapZero;
use invariant lengthIsNotZero;
use invariant validatorsReverseMapValid;
use invariant validatorsReverseMapUniqeness;
use invariant validatorsReverseMapStoresCorrectIndex;
use invariant validatorsReverseMapValidIndex;
use invariant canPayRewardsPot;
use invariant validatorNotThis;
use invariant thisNotValidator;
use invariant validatorHasReverseLookup;
use invariant validatorsRemovalTickNotInTheFuture;
use invariant transactionsTickNotInFuture;
use invariant transactionExist_IFF_notInFuture;
use invariant confirmationsTickNotInFuture;
use invariant transactionsRemovalTickNotInFuture;
use invariant transactionsRemovalTickCorelationTransactionsTick;
use invariant confirmationsTickNotAfterRemoval;
use invariant tickNotZero;
use invariant thisCannotBeCreator;
use invariant emptyTransactionIsEmpty;

// imported from "sanity.spec"
use rule addValidatorSanity;
use rule removeValidatorSanity;
use rule executeTransactionSanity;
use rule voteForTransactionSanity;

// HELPERS
definition filterDef(method f) returns bool = !f.isView;


/* ############ ADD VALIDATOR RULES ############## */

rule addValidatorIntegrity(env e, calldataarg args){
    
    // require invariants in starting state
    allInvariants();
    
    // state before execution
    address a;
    uint256 lengthBefore = currentContract.validators.length;
    bool isAValidatorBefore = currentContract.isValidator[a];

    // execute the method in question
    addValidator(e, args);

    // validate the state after the execution
    assert e.msg.sender == currentContract;
    assert currentContract.validators.length == lengthBefore + 1;
    assert isAValidatorBefore => currentContract.isValidator[a];
    assert !isAValidatorBefore && currentContract.isValidator[a] => currentContract.validators[assert_uint256(currentContract.validators.length - 1)] == a;
}

rule addValidatorDoesNotAffectThirdParty(env e, calldataarg args){
    allInvariants();
    
    address a;
    address b;
    bool isAValidatorBefore = currentContract.isValidator[a];
    bool isBValidatorBefore = currentContract.isValidator[b];

    addValidator(e, args);

    assert (!isAValidatorBefore && currentContract.isValidator[a] && (a != b)) => (isBValidatorBefore == currentContract.isValidator[b]);
}

rule addValidatorChangesQuorum(env e){
    allInvariants();
    
    address a;
    uint256 newQuorum;
    addValidator(e, a, newQuorum);

    assert currentContract.isValidator[a] && currentContract.quorum == newQuorum;
}

rule addValidatorDoesNotChangeConfirmationCount(env e, calldataarg args){
    allInvariants();
    
    address a;
    bytes32 transactionId;
    bool isAValidatorBefore = currentContract.isValidator[a];
    uint256 count = getConfirmationCount(transactionId);

    addValidator(e, args);

    assert count == getConfirmationCount(transactionId);
}


/* ############ REMOVE VALIDATOR RULES ############## */

rule removeValidatorIntegrity(env e, calldataarg args){
    allInvariants();
    
    address a;
    address b;
    uint256 lengthBefore = currentContract.validators.length;
    bool isAValidatorBefore = currentContract.isValidator[a];
    bool isBValidatorBefore = currentContract.isValidator[b];

    removeValidator(e, args);
    
    assert e.msg.sender == currentContract;
    assert currentContract.validators.length == lengthBefore - 1;
    assert !isAValidatorBefore => !currentContract.isValidator[a];
    assert (isAValidatorBefore && !currentContract.isValidator[a] && (a != b)) => (isBValidatorBefore == currentContract.isValidator[b]);
}

rule removeValidatorChangesQuorum(env e){
    allInvariants();
    
    address a;
    uint256 newQuorum;
    removeValidator(e, a, newQuorum);

    assert !currentContract.isValidator[a] && currentContract.quorum == newQuorum;
}

rule removeValidatorCanDecreaseConfirmationCount(env e, calldataarg args){
    allInvariants();
    
    bytes32 transactionId;
    uint256 count = getConfirmationCount(transactionId);

    removeValidator(e, args);

    assert count - 1 == getConfirmationCount(transactionId) || count == getConfirmationCount(transactionId);
}


/* ############ REPLACE VALIDATOR RULES ############## */

rule replaceValidatorIntegrity(env e, calldataarg args){
    allInvariants();
    
    address a;
    address b;
    uint256 lengthBefore = currentContract.validators.length;
    uint256 oldQuorum = currentContract.quorum;
    bool isAValidatorBefore = currentContract.isValidator[a];
    bool isBValidatorBefore = currentContract.isValidator[b];

    replaceValidator(e, args);

    assert e.msg.sender == currentContract;
    assert lengthBefore == currentContract.validators.length;
    assert currentContract.quorum == oldQuorum;
    assert (isAValidatorBefore && !currentContract.isValidator[a] && (a != b)) => (isBValidatorBefore => currentContract.isValidator[b]);
    assert (!isAValidatorBefore && currentContract.isValidator[a] && (a != b)) => (!isBValidatorBefore => !currentContract.isValidator[b]);
}


/* ############ CHANGE QUORUM RULES ############## */

rule changeQuorumIntegrity(env e){
    allInvariants();
    
    uint256 newQuorum;
    changeQuorum(e, newQuorum);

    assert e.msg.sender == currentContract;
    assert newQuorum == currentContract.quorum;
}

/* ############ CREATE TRANSACTION RULES ############## */

rule createTransactionIntegrity(env e, calldataarg args){
    allInvariants();

    bytes32 transactionId;
    address destination;
    uint256 value;
    bytes data;
    bool hasReward;

    uint256 totalValueBefore = currentContract.transactionsTotalValue;
    uint256 pendingRewardsPotBefore = currentContract.pendingRewardsPot;
    bool transactionExistsBefore = transactionExists(transactionId);

    createTransaction(e, transactionId, destination, value, data, hasReward);

    assert !transactionExistsBefore => transactionExists(transactionId) ;
    assert e.msg.value >= value && (hasReward => e.msg.value >= value + FEE());
    assert currentContract.pendingRewardsPot == (hasReward ? pendingRewardsPotBefore + FEE() : pendingRewardsPotBefore);
    assert currentContract.transactionsTotalValue == totalValueBefore + value;
    assert tick() == currentContract.transactionsTick[transactionId] + 1; 

}

rule anyoneCanCallCreateTransaction(env e, env e2, calldataarg args){
    allInvariants();

    require nativeBalances[e.msg.sender] == nativeBalances[e2.msg.sender];
    require e.msg.value == e2.msg.value;
    require e.msg.sender != currentContract;
    require e2.msg.sender != currentContract;

    // save the status of the storage in init
    storage init = lastStorage;

    // execute method once
    createTransaction(e, args);

    // execute method on same storage as before the first transaction including reverting paths
    createTransaction@withrevert(e2, args) at init;

    // ensure the last method call did not revert
    assert !lastReverted;
}

/* ############ VOTE FOR TRANSACTION RULES ############## */

rule voteForTransactionIntegrity(env e){
    allInvariants();

    bytes32 transactionId;
    address destination;
    uint256 value;
    bytes data;
    bool hasReward;

    bool isValidatorBefore = currentContract.isValidator[e.msg.sender];
    bool isExistedBefore = transactionExists(transactionId);
    address destinationBefore = currentContract.transactions[transactionId].destination;
    uint256 confirmationCountBefore = getConfirmationCount(transactionId);
    uint256 transactionsTotalValueBefore = currentContract.transactionsTotalValue;
    
    voteForTransaction(e, transactionId);

    assert isValidatorBefore;
    assert (isExistedBefore && destinationBefore != currentContract) => transactionExists(transactionId);
    assert currentContract.confirmations[transactionId][e.msg.sender] == true 
            || currentContract.transactions[transactionId].executed 
            || !transactionExists(transactionId);
    assert getConfirmationCount(transactionId) == confirmationCountBefore + 1 
            || currentContract.transactions[transactionId].executed 
            || !transactionExists(transactionId);
    assert currentContract.confirmationsTick[transactionId][e.msg.sender] < tick();
}

rule voteForTransactionRevertConditions(env e){
    allInvariants();

    bytes32 transactionId;
    address destination;
    uint256 value;
    bytes data;
    bool hasReward;

    bool alreadyConfirmed = currentContract.confirmations[transactionId][e.msg.sender] && 
        currentContract.confirmationsTick[transactionId][e.msg.sender] >= currentContract.transactionsTick[transactionId] &&
        currentContract.confirmationsTick[transactionId][e.msg.sender] > currentContract.validatorsRemovalTick[e.msg.sender];
    bool msgSenderIsValidator = currentContract.isValidator[e.msg.sender];
    bool nullTransaction = transactionId == to_bytes32(0);
    bool transactionExists = transactionExists(transactionId);
    bool msgValue = e.msg.value != 0;
    bool reentrancy = currentContract.guard != 1;
    bool overflow = tick() + 1 < tick() || tick() + 2 < tick();

    voteForTransaction@withrevert(e, transactionId);

    bool revertConditions = !msgSenderIsValidator || nullTransaction || !transactionExists || alreadyConfirmed || msgValue || reentrancy || overflow;

    assert revertConditions => lastReverted;

}

rule voteForTransactionDoesNotAffectThirdParty(env e){
    allInvariants();

    address a;
    bytes32 id2;
    bytes32 id;

    require a != e.msg.sender || id != id2;

    bool voteBefore = currentContract.confirmations[id2][a];
    uint256 confirmationsTickOfA = currentContract.confirmationsTick[id2][a];

    voteForTransaction(e, id);

    assert voteBefore == currentContract.confirmations[id2][a];
    assert confirmationsTickOfA == currentContract.confirmationsTick[id2][a];
}

/* ############ EXECUTE TRANSACTION RULES ############## */

rule anyoneCanCallExecuteTransaction(env e, env e2, calldataarg args){
    allInvariants();

    require (e.msg.value == e2.msg.value);
    require e2.msg.sender != e.msg.sender;

    uint256 sum = require_uint256(confirmedRewardsPot() + FEE());
    require pendingRewardsPot() >= 2 * FEE();

    storage init = lastStorage;

    executeTransaction(e, args);

    executeTransaction@withrevert(e2, args) at init;

    assert !lastReverted;
}

rule executeTransactionIntegrity(env e){
    allInvariants();
    
    bytes32 transactionId;
    bool executedBefore = currentContract.transactions[transactionId].executed;
    uint256 balanceBefore = nativeBalances[currentContract];
    uint256 confirmedRewardsPotBefore = confirmedRewardsPot();
    bool isConfirmedBefore = isConfirmed(transactionId);
    
    executeTransaction(e, transactionId);
    
    assert !executedBefore;
    assert currentContract.transactions[transactionId].executed => isConfirmedBefore;
    assert (currentContract.transactions[transactionId].executed && 
            currentContract.transactions[transactionId].hasReward) => (
                confirmedRewardsPotBefore + FEE() <= confirmedRewardsPot()
            );
    assert (currentContract.transactions[transactionId].destination != currentContract && currentContract.transactions[transactionId].executed) => (to_mathint(balanceBefore) - to_mathint(nativeBalances[currentContract])) <= currentContract.transactions[transactionId].value;
}

/* ############ REMOVE TRANSACTION RULES ############## */

rule removeTransactionIntegrity(env e){
    allInvariants();
    
    bytes32 transactionId;
    bool isExistedBefore = currentContract.transactions[transactionId].destination != 0;
    uint256 lengthBefore = currentContract.transactionIds.length;

    removeTransaction(e, transactionId);

    assert e.msg.sender == currentContract;
    assert isExistedBefore && currentContract.transactions[transactionId].destination == 0;
    assert lengthBefore - 1 == currentContract.transactionIds.length;
}


rule removeTransactionRefundsCreator(env e){
    allInvariants();

    bytes32 transactionId;
    address creator = currentContract.transactions[transactionId].creator;
    uint256 creatorBalanceBefore = nativeBalances[creator];
    uint256 transactionCost = require_uint256(currentContract.transactions[transactionId].value + (currentContract.transactions[transactionId].hasReward?(FEE()):0));
    bool isExecuted = currentContract.transactions[transactionId].executed;

    removeTransaction(e, transactionId);

    assert !isExecuted => creatorBalanceBefore + transactionCost == nativeBalances[creator];
}


/* ############ DISTRIBUTE REWARD RULES ############## */

rule distributeRewardsCorrectDecrease(env e, calldataarg args){
    allInvariants();
    
    uint256 oldRewards = confirmedRewardsPot();
    require currentContract.validators.length != 1;

    distributeRewards(e, args);

    assert confirmedRewardsPot() == oldRewards % (currentContract.validators.length - 1);
}

/* ############ VALID STATE CHANGES ############## */
rule onlyMethodsCanChangeNumberOfValidator(env e, method f)filtered { f -> filterDef(f)}{
    allInvariants();
    
    calldataarg args;
    uint256 lengthBefore = currentContract.validators.length;

    f(e, args);

    assert lengthBefore < currentContract.validators.length => 
        f.selector == sig:addValidator(address, uint256).selector || 
        f.selector == sig:executeTransaction(bytes32).selector || 
        f.selector == sig:voteForTransaction(bytes32).selector;
}

rule tickCannotDecrease(method f, env e, calldataarg args){
    
    uint256 tickBefore = tick();
    
    f(e, args);

    assert tick() >= tickBefore;
}