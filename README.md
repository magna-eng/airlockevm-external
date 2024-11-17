# Airlock EVM External

This repository contains the a flattened version of our MerkleVester airlock protocol.


# 1. Overview

This repo contains a flattened version of the MerkleVester token vester contracts. Vester contracts lock tokens and gradually make them available to users as time goes on. Vester contracts internally operates on allocations which is a combination of a vesting schedule and metadata like the owner of the allocation or the total amount of tokens withdrawn from the allocation. It is a Merkle Root based vester contract meaning that it can provide gas savings when the number of allocations are high.

## 1.1 Types of vesting schedules

There are two types of schedules implemented.

### 1.1.1 Calendar schedules

```solidity
/**
 * @notice Immutable unlock schedule for calendar allocations
 * @dev solidity does not support immutablability outside of compile time, contracts must not implement mutability
 *
 * @param unlockScheduleId id of the allocation
 * @param unlockTimestamps sequence of timestamps when funds will unlock
 * @param unlockPercents sequence of percents that unlock at each timestamp, in 10,000ths
 */
struct CalendarUnlockSchedule {
    string unlockScheduleId;
    uint32[] unlockTimestamps;
    uint256[] unlockPercents;
}
```
Calendar schedules can be thought of as a sequence of pairs of timestamp and percents, for example:

| Timestamp | Percent |
| --------  | ------- |
| 1000      | 0       |
| 1500      | 20      |
| 2000      | 80      |
| 3000      | 100     |

Based on the current timestamp and the schedule, the unlocked amount can be calculated. For example based on the example above at timestamp 1600, 20% of the total allocation would be unlocked.

### 1.1.2 Interval schedules
```solidity
/**
 * @notice Immutable unlock schedule for interval allocations
 * @dev solidity does not support immutablability outside of compile time, contracts must not implement mutability
 *
 * @param unlockScheduleId id of the allocation
 * @param pieces sequence of pieces representing phases of the unlock schedule, percents of pieces must sum to 100%
 */
struct IntervalUnlockSchedule {
    string unlockScheduleId; // Workaround for Internal or recursive type is not allowed for public state variables
    Piece[] pieces;
}

/**
 * @notice Represents a phase of an interval unlock schedule
 * @dev solidity does not support immutablability outside of compile time, contracts must not implement mutability
 *
 * @param startDate start timestamp of the piece
 * @param periodLength time length of the piece
 * @param numberOfPeriods how many periods for this piece
 * @param percent the total percent, in 10,000ths that will unlock over the piece
 */
struct Piece {
    uint32 startDate;
    uint32 periodLength;
    uint32 numberOfPeriods;
    uint32 percent;
}
```
Interval schedules can be thought of as a more granular version of Calendar schedules where individual rows in a calendar schedule can be subdivided into a piece with multiple periods. For example the period between 1500 and 2000 could be subdiveded into a piece with 50 periods, each period lasting 10 seconds.


| Start date | Period Length | Number of periods | Percent |
| ---------- | ------------- | ----------------- | ------- |
| 1000       | 10            | 50                | 20      |
| 1500       | 10            | 50                | 80      |
| 2000       | 100           | 5                 | 100     |

For example based on the example above at timestamp 1600, 32% (20% + (60% * 0.2) = 32%) of the total allocation would be unlocked.

## 1.2 Noteable features

### 1.2.1 Pay fee on claim
Fee can be set and collected during withdrawing vested tokens from the contract. Fee currently can only be taken in Eth.

### 1.2.2 Cancel an allocation
If the allocation is cancellable, then the benefactor can cancel an allocation. Already vested funds remain withdrawable to the beneficiary

### 1.2.3 Revoke an allocation
If the allocation is revokable, then the benefactor can revoke an allocation. Unwithdrawn funds are no longer withdrawable to the beneficiary.
