# Capture the Spec

Welcome to the **Capture the Spec** contest! This event is challenges participants to demonstrate their Solidity and formal verification skills in a fun environment using the Certora Prover.

## Table of Contents
- [Contest Overview](#contest-overview)
- [Rules](#rules)
- [How to Participate](#how-to-participate)
- [Submission Guidelines](#submission-guidelines)
- [Prizes](#prizes)
- [Contact](#contact)

## Contest Overview

In this contest, participants will receive a formal specification of a Solidity contract expressed in the Certora Verification Language (CVL). Your task is to write a Solidity contract that satisfies all the rules and invariants defined in the specification, which will be verified using the Certora Prover.

### Specification Breakdown
The specification is divided into three parts:
1. **main multisig.spec**: Contains all integrity rules showcasing what each function of the contract should do.
2. **invariant.spec**: Demonstrates inductive properties of the contract.
3. **sanity.spec**: Outlines rules that show legal paths of the contract.

The contest will take place during DSS from **November 7 to November 9**.

## Rules

1. **Eligibility**: Open to all participants.
2. **Original Work**: All submissions must be the original work of the participant or team.
3. **Verification**: Participants must ensure that their contracts verify all rules and invariants using the Certora Prover. You can configure the prover using the `run.conf` file provided.
4. **Judging Criteria**: The primary judging criteria will be based on the verification of all rules. If no participant verifies all rules, the top 3 submissions will be awarded based on partial verification (highest number of verified rules).

## How to Participate

1. **Read the Documentation**: Familiarize yourself with the [Certora Verification Language](https://docs.certora.com/).
2. **Set Up Your Environment**: Prepare your development environment to write and verify Solidity contracts using the Certora Prover.
3. **Develop Your Contract**: Create a Solidity contract that meets all specified rules and invariants.
4. **Run the Prover**: Use the provided `run.conf` file to run the Certora Prover and verify your contract.

## Submission Guidelines

Submissions must be made via a Google Form. Include the link to your verification run of the Certora Prover in your submission. The form can be found here: [Google Form Link Placeholder].

## Prizes

- **1st, 2nd, and 3rd Place**: $1000 each for the three fastest participants/teams who successfully write a contract that verifies all rules. If no one can verify all rules and invariants, the top 3 submissions based on partial verification will win.
- **Bonus Prize**: An additional $500 will be awarded to the three fastest participants who achieve low live statistics on the following specific rules:
  - Rule 1: [Placeholder for Rule Name]
  - Rule 2: [Placeholder for Rule Name]
  - Rule 3: [Placeholder for Rule Name]

## Contact

For any questions or concerns, please reach out to us at [contest-email@certora.com](mailto:contest-email@certora.com).

---

Good luck, and may the best team win!