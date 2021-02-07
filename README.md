# lean4-assert-command
A simple assertion command for Lean4.

## Usage


Assert standard boolean (`BEq`) equality by using `#assert TERM == TERM`:

<img src="https://github.com/pnwamk/lean4-assert-command/blob/docs/ex_assert.png?raw=true" alt="Passing assertions are underlined in green and report success." width="350"/>

Assert equality with a custom predicate using `#assert TERM == TERM via PRED`:

<img src="https://github.com/pnwamk/lean4-assert-command/blob/docs/ex_assert_via.png?raw=true" alt="Passing assertions with custom equality are underlined in green and report the success and custom equality function." width="350"/>

Failed assertions are highlighted and show actual and expected values:

<img src="https://github.com/pnwamk/lean4-assert-command/blob/docs/ex_failed_assert.png?raw=true" alt="Failed assertions are underlined in red and report the terms' values." width="350"/>
