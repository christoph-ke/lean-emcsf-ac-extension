module

public import EmcsfAcExtension.Global.Calculus.CurveTrace

/-! # The alternative fixed-representation chain-rule route

The landed calculus proves the fixed-density primitive chain rule and
glues proper rectangle charts over the actual boundary segment. These
canonical route names expose that existing proof. The selected internal project record
consumer in `Frontier` continues to prove AC through the improved label.
Source: `charged_SF_new_version.tex:L1410–L1415`.
-/

public section

namespace EmcsfAcExtension.Global.Exterior

/-- [node c:exterior#representation-chain-rule-bridge]
The fixed-density primitive, its continuous incoming derivative, and
proper local label changes give the boundary AC chain rule. The common
initial density is fixed before the boundary parameter. Proper rectangle
charts are glued in the landed calculus; no global enclosing rectangle
or new regularity hypothesis is assumed. There are no estimate constants.
-/
alias representation_chain_rule_bridge := Calculus.timelike_ac_chain_rule

/-- [node c:exterior#chain-rule-from-representation]
The alternative representation route gives the AC trace and prescribed
density chain rule on every proper increasing bi-Lipschitz boundary.
For a frontier or cylinder take the incoming parametrization to be `id`.
This is an available alternative, with no role as an additional premise
of the selected internal project record route. No constants occur in the identity.
-/
alias chain_rule_from_representation := representation_chain_rule_bridge

end EmcsfAcExtension.Global.Exterior
