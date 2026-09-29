import ForestUnimodality.BridgeFlowData.Stage99.Cell123Term02.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell123Term02
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=12 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (2149098044745697948987499600016596671/400000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (16516858795157707270559341113371009438053/10000000000000000000000000000000000000000)

def table : Table :=
  ⟨12, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨3, (-568979211227971/750000000000000), 64, (23415168927861797289197615100269702091578904408833/50000000000000000000000000000000000000000000000000), (46830337855723594578395230200539404183157808817667/100000000000000000000000000000000000000000000000000)⟩, (12837837850675680290362655877317879801135581719771325181273118218319559344831562082512352313466423699390163961212699138238067975487784042844402145537/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (102702702805405442322901247018543038409084653758177180691815989401631009098903908867218478092271654473156816793776748360899398860179534959651144679963/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

theorem header_checked : table.headerCheck=true := by decide +kernel

theorem connections_checked : (List.range table.n).all table.connectionCheck=true := by decide +kernel

theorem table_rows_checked : (List.range table.n).all (fun i=>(table.row i).check table.environment)=true := by

  apply List.all_eq_true.mpr
  intro i hi
  apply check_getD rows Batch000.row000 environment rows_checked i
  rw [rows_length]
  exact List.mem_range.mp hi

#print axioms header_checked

#print axioms connections_checked

#print axioms table_rows_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell123Term02
