import Rel.Lang.Test.Common
import Rel.Lang.Test.Blocks
import Rel.Lang.Test.Orders
import Rel.Lang.Test.TwoIdx
import Rel.Lang.Test.Folds
import Rel.Lang.Test.RoundTrip
import Rel.Lang.Test.Lists
import Rel.Lang.Test.Arith
import Rel.Lang.Test.Literals
import Rel.Lang.Test.Chs
import Rel.Lang.Test.Prelude
import Rel.Lang.Test.Fixpoints
import Rel.Lang.Test.MuGrow
import Rel.Lang.Test.AC
import Rel.Lang.Test.Kern2
import Rel.Lang.Test.Kern45
import Rel.Lang.Test.Kern68
import Rel.Lang.Test.KernRows
import Rel.Lang.Test.Kern9
import Rel.Lang.Test.KernMap

/-! The Rel language on the blocks world of `doc/rel-lang-design.md` §g, the program `Programs.blocks`; its
    front-end errors; the round trip of `rel_program`'s grammar on every operator of §b. Every program runs as its
    expansion (`rel_program`, `Expand`): its definitions `n.expanded`, its prints `n.prints`, its checks and ok bits
    `n.failures`, `n.ok`; a front-end error is read off statements by `Expand.read`, which evaluates nothing.
    The tests are split by subject into `Rel/Lang/Test/*.lean`, so that the parts build in parallel. -/
