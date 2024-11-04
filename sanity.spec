rule addValidatorSanity(env e, calldataarg args){
    allInvariants();
    
    address a;
    bool isValidatorBefore = currentContract.isValidator[a];
    uint256 lengthBefore = currentContract.validators.length;

    addValidator(e, args);

    satisfy lengthBefore < currentContract.validators.length;
    satisfy !isValidatorBefore && currentContract.isValidator[a];
}

rule removeValidatorSanity(env e, calldataarg args){
    allInvariants();
    
    address a;
    bool isValidatorBefore = currentContract.isValidator[a];
    
    bytes32 transactionId;
    uint256 count = getConfirmationCount(transactionId);

    removeValidator(e, args);

    satisfy isValidatorBefore && !currentContract.isValidator[a];
    satisfy count - 1 == getConfirmationCount(transactionId);
    satisfy count == getConfirmationCount(transactionId);
}

rule executeTransactionSanity(env e){
    allInvariants();
    
    uint256 lengthBefore = currentContract.validators.length;

    bytes32 transactionId;
    executeTransaction(e, transactionId);

    satisfy lengthBefore < currentContract.validators.length;
    satisfy currentContract.transactions[transactionId].executed && !isConfirmed(transactionId);
}

rule voteForTransactionSanity(env e){
    allInvariants();
    
    bytes32 transactionId;

    uint256 lengthBefore = currentContract.validators.length;
    bool isValidatorBefore = currentContract.isValidator[e.msg.sender];
    address destinationBefore = currentContract.transactions[transactionId].destination;
    uint256 confirmationCountBefore = getConfirmationCount(transactionId);
     bool isConfirmedBefore = isConfirmed(transactionId);
    bool isExecutedBefore = currentContract.transactions[transactionId].executed;

    voteForTransaction(e, transactionId);

    satisfy lengthBefore < currentContract.validators.length;
    satisfy isValidatorBefore && !currentContract.isValidator[e.msg.sender];

    satisfy currentContract.confirmationsTick[transactionId][e.msg.sender] < tick() - 2;

    satisfy ((destinationBefore != currentContract) && (currentContract.transactions[transactionId].destination != currentContract)) && confirmationCountBefore + 1 == getConfirmationCount(transactionId);

    satisfy !isConfirmedBefore && isConfirmed(transactionId) && isExecutedBefore && currentContract.transactions[transactionId].executed;
    satisfy !isConfirmedBefore && isConfirmed(transactionId) && !currentContract.transactions[transactionId].executed;
}
