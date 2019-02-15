import system.io
import .translation_tptp
import .problem_translation

--###################
--## IMPORT/EXPORT ##
--###################
-- -> Started but currently stopped. Will be continued after other points are done
open io
open io.fs

meta def export_format (f : format) : io unit := put_str f.to_string

/- run_cmd do ⟨f,_⟩ <- using_hammer $ problem_to_format [`sum_two, `fib] [`(Π(x:ℕ), x + x = 2 * x), `(2*1 = 2), `(1+2=3), `(1:ℕ), `(2:ℕ)] `((1+1 = 2)),
           let io_output := export_format f,
           let file_handle := mk_file_handle "test.tptp" io.mode.write tt,
           -- let p := write file_handle "test" ,
           tactic.skip -/