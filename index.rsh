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

const board_single = array(Bool,
    [false, false, false,
        false, false, false,
        false, false, false,]);

const board_total = array(Single,
    [board_single, board_single, board_single,
        board_single, board_single, board_single,
        board_single, board_single, board_single]);

const create_initial_state = (is_x_first) => ({
    xs_turn: is_x_first,
    xs: board_total,
    os: board_total,
    result: {
        xs: board_single,
        os: board_single,
    },
});

// Check both singles, return if cell is occupied
// single : Single
// j : jth cell in Single
const cell_both = (single1, single2, j) => //??
    (single1[j] || single2[j]);

// Return a Single showing which cells are empty
// state : State
// i : ith Single in total
const marks_all = (single1, single2) =>
    array(Bool,
        [cell_both(single1, single2, 0), cell_both(single1, single2, 1), cell_both(single1, single2, 2),
        cell_both(single1, single2, 3), cell_both(single1, single2, 4), cell_both(single1, single2, 5),
        cell_both(single1, single2, 6), cell_both(single1, single2, 7), cell_both(single1, single2, 8)]);

// Return index of a cell by its cons
const cell = (row, col) => col + row * COLS;

// Return if a sequence is matching
// single : Single
// dRow : change in rows
// dCol : change in columns
const seq = (single, row, col, dRow, dCol) =>
(single[cell(row, col)] &&
    single[cell(row + dRow, col + dCol)] &&
    single[cell(row + dRow + dRow, col + dCol + dCol)]);

// Special cases of sequences
const row = (single, row) => seq(single, row, 0, 0, 1);
const col = (single, col) => seq(single, 0, col, 1, 0);

// Return if single has any winning pairs
// single : Single
const winning_pair = (single) =>
(row(single, 0) || row(single, 1) || row(single, 2) ||
    col(single, 0) || col(single, 1) || col(single, 2) ||
    seq(single, 0, 0, 1, 1) ||
    seq(single, 0, 2, 1, -1));

// Return if the single is filled
// single : Single
const single_filled = (single) =>
(single[0] && single[1] && single[2] &&
    single[3] && single[4] && single[5] &&
    single[6] && single[7] && single[8]);

// Return if the single is either won by a side or is filled completely
// If false, it means there are still rounds to play
// state : State
// i : ith Single in Total
const single_done = (single1, single2) =>
(winning_pair(single1)
    || winning_pair(single2)
    || single_filled(marks_all(single1, single2)));

// Legal move is a possible move between 0 and 8,
// Valid move is a move to a empty cell
// i : ith Single in Total
const legalMove = (move) => (0 <= move && move < CELLS);
const validMove = (state, move, i) => (!cell_both(state.xs[i], state.os[i], move));

// Get a valid move from the frontend
// A valid move contains an i number indicating the Single
// and a move indicating the index of the move
function getValidMove(interact, state, i) {
    const _move = interact.getMove(state);
    assume(legalMove(_move));
    assume(validMove(state, _move, i));

    return declassify(_move);
}

function getLegalSingle(interact, state) {
    const _single = interact.getSingle(state);
    assume(legalMove(_single));

    return declassify(_single);
}

// Change the ith Single's move indexed boolean to true
// Return the changed State
function applyMove(state, move, i) {
    require(legalMove(move) && legalMove(i));
    require(validMove(state, move, i));
    const turn = state.xs_turn;

    // Check if the move cell is empty
    require(!(cell_both(state.xs[i], state.os[i], move)));

    return {
        xs_turn: !turn,
        xs: (turn ? state.xs[i].set(move, true) : state.xs),
        os: (turn ? state.os : state.os[i].set(move, true)),
        result: state.result,
    };
}

const winner_is_x = (state, i) => winning_pair(state.xs[i]);
const winner_is_o = (state, i) => winning_pair(state.os[i]);

// Timeout Delay
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
}

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

            var state = create_initial_state(x_is_first);            // while results board isn't done:
            invariant((balance() == (2 * wagerAmount)));
            while (!single_done(state.result.xs, state.result.os)) {
                if (state.xs_turn) {
                    commit();
                    // A chooses a single
                    A.only(() => {
                        const singleA = getLegalSingle(interact, state);

                        // A chooses a move
                        const moveA = getValidMove(interact, state, singleA);
                    });
                    A.publish(singleA, moveA);

                    // if valid make the move (X)
                    // else give an error
                    state = applyMove(state, moveA, singleA);

                    // if the single is filled after move:
                    if (single_done(state.xs[singleA], state.os[singleA])) {
                        // if A wins:
                        if (winner_is_x(state, singleA)) {
                            // ​change the single in results board to X
                            state.result.xs[singleA] = true;
                        }
                        // else if B wins:
                        else if (winner_is_o(state, singleA)) {
                            // change the single in results board to O
                            state.result.os[singleA] = true;
                        }
                        // else (draw):
                        else {
                            // ​TODO: make a coin flip to decides who wins the board
                        }
                    }

                    // This is the Single A's decision has led to.
                    const ledSingle = { xs: state.xs[moveA], os: state.os[moveA] };

                    // if the single A's decision has led is full:
                    if (single_done(ledSingle.xs, ledSingle.os)) {
                        // B chooses a single
                        B.only(() => {
                            const singleB = getLegalSingle(interact, state);
                        });
                    }
                    continue;
                }
                else {
                    commit();
                    continue;
                }
            }



            // ​    - if B chooses a full single

            // ​     - give error

            // ​    - else

            // ​     - choose it

            // B chooses a move

            // - if valid make the move (O)

            // - else give an error



            // - if the single is filled after move:

            // - if A wins:

            // ​    change the single in results board to X

            // - else if B wins:

            // ​    change the single in results board to O

            // - else (draw):

            // ​    make a coin flip to decides who wins the board

            // check the results board

            // transfer balance depending on the result (A wins | B wins | draw).
            exit();
        });