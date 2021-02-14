'reach 0.1';

const ROWS = 3;
const COLS = 3;
const CELLS = ROWS * COLS;

const Single = Array(Bool, CELLS);
const Total = Array(Single, CELLS);

const ResultState = Object({
    xs: Single,
    os: Single,
});

const State = Object({
    xs_turn: Bool,
    xs: Total,
    os: Total,
    result: ResultState,
});

/**
 * @type Single
 */
const board_single = array(Bool, [
    false, false, false,
    false, false, false,
    false, false, false,
]);

/**
 * @type Total
 */
const board_total = array(Single, [
    board_single, board_single, board_single,
    board_single, board_single, board_single,
    board_single, board_single, board_single,
]);

const create_initial_state = (is_x_first) => ({
    xs_turn: is_x_first,
    xs: board_total,
    os: board_total,
    result: {
        xs: board_single,
        os: board_single,
    },
});

/**
 * Return if both singles are true at given index
 * @param single1 Single
 * @param single2 Single
 * @param j int
 */
const cell_both = (single1, single2, j) =>
    (single1[j] || single2[j]);

/**
 * Return a Single showing which cells are empty
 * @param single1 Single
 * @param single2 Single
 */
const marks_all = (single1, single2) =>
    array(Bool,
        [cell_both(single1, single2, 0), cell_both(single1, single2, 1), cell_both(single1, single2, 2),
        cell_both(single1, single2, 3), cell_both(single1, single2, 4), cell_both(single1, single2, 5),
        cell_both(single1, single2, 6), cell_both(single1, single2, 7), cell_both(single1, single2, 8)]);

/**
 * Return index of a cell by its col's
 * @param row UInt
 * @param col UInt
 */
const cell = (row, col) => col + row * COLS;

/**
 * Return if a sequence is matching
 * @param single Single
 * @param row UInt
 * @param col UInt
 * @param dRow UInt
 * @param dCol UInt
 */
// const seq = (single, row, col, dRow, dCol) => (
//     single[cell(row, col)] &&
//     single[cell(row + dRow, col + dCol)] &&
//     single[cell(row + dRow + dRow,  col + dCol + dCol)]
// );

const op = (op, x) => (y) => op(x, y);

const seq = (b, r, c, dr, dc) =>
      (b[cell(r, c)] &&
       b[cell(r+dr, dc(c))] &&
       b[cell(r+dr+dr, dc(dc(c)))]);

// Special cases of sequences
const row = (b, r) => seq(b, r, 0, 0, op(add, 1));
const col = (b, c) => seq(b, 0, c, 1, op(add, 0));
/**
 * Return if the single is filled
 * @param single Single
 */
const winning_pair = (b) =>
      (row(b, 0) || row(b, 1) || row(b, 2) ||
       col(b, 0) || col(b, 1) || col(b, 2) ||
       seq(b, 0, 0, 1, op(add, 1)) ||
       seq(b, 0, 2, 1, op(sub, 1)));
       
/**
 * Return if the single is filled
 * @param single Single
 */
const single_filled = (single) => (
    single[0] && single[1] && single[2] &&
    single[3] && single[4] && single[5] &&
    single[6] && single[7] && single[8]
);

/**
 * Return if the single is either won by a side or is filled completely.
 * If false, it means there are still rounds to play
 * @param single1 Single
 * @param single2 Single
 * 
 * @return Boolean
 */
const single_done = (single1, single2) => (
    winning_pair(single1) ||
    winning_pair(single2) ||
    single_filled(marks_all(single1, single2))
);

/**
 * Return if move is between 0 and 8
 * @param move UInt
 */
const legalMove = (move) => (0 <= move && move < CELLS);

/**
 * Return if move is to an empty cell
 * @param state State
 * @param move UInt
 * @param i UInt
 */
const validMove = (state, move, i) => (!cell_both(state.xs[i], state.os[i], move));

/**
 * Get a valid move from the frontend
 * @param interact Frontend
 * @param state State
 * @param i UInt
 * 
 * @returns UInt, a valid move
 */
function getValidMove(interact, state, i) {
    const _move = interact.getMove(state);
    assume(legalMove(_move));
    assume(validMove(state, _move, i));

    return declassify(_move);
}

/**
 * Return a legal Single index.
 * @param interact Frontend
 * @param state State
 * 
 * @returns UInt, a legal Single
 */
function getLegalSingle(interact, state) {
    const _single = interact.getSingle(state);
    assume(legalMove(_single));

    return declassify(_single);
}

/**
 * Change the ith Single's move indexed boolean to true.
 * @param state State
 * @param move UInt
 * @param i UInt
 * 
 * @return The changed State
 */
function applyMove(state, move, i) {
    require(legalMove(move) && legalMove(i));
    require(validMove(state, move, i));
    const turn = state.xs_turn;

    // Check if the move cell is empty
    require(!(cell_both(state.xs[i], state.os[i], move)));

    return {
        xs_turn: !turn,
        xs: (turn ? state.xs.set(i, state.xs[i].set(move, true)) : state.xs),
        os: (turn ? state.os : state.os.set(i, state.os[i].set (move, true))),
        result: state.result,
    };
}

const winner_is_x = (state, i) => winning_pair(state.xs[i]);
const winner_is_o = (state, i) => winning_pair(state.os[i]);

const result_is_x = (state) => winning_pair(state.result.xs);
const result_is_o = (state) => winning_pair(state.result.os);

const DELAY = 20;

const Player = {
    ...hasRandom,
    getMove: Fun([State], UInt),
    getSingle: Fun([State], UInt),
    endsWith: Fun([State], Null),
};

const Alice = {
    ...Player,
    getWager: Fun([], UInt),
};

const Bob = {
    ...Player,
    acceptWager: Fun([UInt], Null),
};

export const main =
    Reach.App(
        {},
        [['Alice', Alice], ['Bob', Bob]],
        (A, B) => {
            // A wagers and flips a coin
            A.only(() => {
                const wagerAmount = declassify(interact.getWager());
                const _coinFlipA = interact.random();
                const commitA = declassify(digest(_coinFlipA));
            });
            A.publish(wagerAmount, commitA)
                .pay(wagerAmount);
            commit();

            // B accepts wager and flips a coin
            B.only(() => {
                interact.acceptWager(wagerAmount);
                const coinFlipB = declassify(interact.random());
            });
            B.publish(coinFlipB)
                .pay(wagerAmount);
            commit();

            // A decrypts the coin flip
            A.only(() => {
                const coinFlipA = declassify(_coinFlipA);
            });
            A.publish(coinFlipA);

            // Make sure it is well encrypted
            require(commitA == digest(coinFlipA));

            const x_is_first = (((coinFlipA % 2) + (coinFlipB % 2)) % 2) == 0;

            // ! This part gives errors
            var state = create_initial_state(x_is_first);
            invariant((balance() == (2 * wagerAmount)));
            while (!single_done(state.result.xs, state.result.os)) {
                // TODO: Set A's or B's move and results in a single assignment
                if (state.xs_turn) {
                    commit();
                    // ? A chooses a single
                    A.only(() => {
                        const singleA = getLegalSingle(interact, state);
                        // A chooses a move
                        const moveA = getValidMove(interact, state, singleA);
                    });
                    A.publish(singleA, moveA);

                    const setup = applyMove(state, moveA, singleA);

                    commit();

                    // ? This is the Single A's decision has led to.
                    const ledSingle = { xs: (setup.xs[moveA]), os: (setup.os[moveA]), };
                    if (single_done(ledSingle.xs, ledSingle.os)) {
                        B.only(() => {
                            const singleB = getLegalSingle(interact, setup);
                            assume(!single_done(setup.xs[singleB], setup.os[singleB]));
                        });
                        B.publish(singleB);
                    }
                    else {
                        B.only(() => {
                        });
                        B.publish();
                        const singleB = moveA;
                    }

                    // ? A makes move, Single is filled
                    if (single_done(setup.xs[singleA], setup.os[singleA])) {
                        // if A wins:
                        state = {
                            xs_turn: state.xs_turn,
                            xs: state.xs,
                            os: state.os,
                            result: {
                                xs: (winner_is_x(setup, singleA) ? setup.result.xs.set(singleA, true) : state.result.xs),
                                os: (winner_is_x(setup, singleA) ? state.result.os : setup.result.os.set(singleA, true)),
                            }
                        };
                        continue;
                    }
                    // ? A makes move, Single is not filled
                    state = setup;
                    continue;
                } else {
                    // ! single B in the consensus doesn't transfer here.
                    commit();
                    // B chooses a move
                    B.only(() => {
                        const moveB = getValidMove(interact, state, singleB);
                    });
                    B.publish(moveB);

                    const setup = applyMove(state, moveB, singleB);

                    // This is the Single B's decision has led to.
                    const ledSingle = { xs: (setup.xs[moveB]), os: (setup.os[moveB]), };

                    if (single_done(ledSingle.xs, ledSingle.os)) {
                        A.only(() => {
                            const singleA = getLegalSingle(interact, setup);
                            assume(!single_done(setup.xs[singleA], setup.os[singleA]));
                        });
                        A.publish(singleA);
                    }
                    else {
                        A.only(() => {
                            const _singleA = moveB;
                            const singleA = declassify(_singleA);
                        });
                        A.publish(singleA);
                    }

                    if (single_done(setup.xs[singleB], setup.os[singleB])){
                        if (winner_is_o(setup, singleA)) {
                            const setupFinal = {
                                xs: setup.xs,
                                os: setup.os,
                                result: {
                                    xs: setup.xs,
                                    os: setup.os.set(singleA, true),
                                }
                            };
                            state = setupFinal;
                            continue;
                        }
                    } else {
                        // TODO: Make a coinflip here
                        const setupFinal = {
                            xs: setup.xs,
                            os: setup.os,
                            result: {
                                xs: setup.xs.set(singleA, true),
                                os: setup.os,
                            }
                        };
                        state = setupFinal;
                        continue;
                    }

                    state = setup;
                    continue;
                }
            }
            
            const [toA, toB] = (result_is_x(state) ? [2, 0]
            : (result_is_o(state) ? [0, 2]
                : [1, 1]));

            transfer(toA * wagerAmount).to(A);
            transfer(toB * wagerAmount).to(B);
            commit();

            // Check the results board
            each([A, B], () => {
                interact.endsWith(state);
            });

            exit();
        });