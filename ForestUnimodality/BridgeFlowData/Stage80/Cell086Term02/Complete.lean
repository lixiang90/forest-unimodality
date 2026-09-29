import ForestUnimodality.BridgeFlowData.Stage80.Cell086Term02.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell086Term02
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=29 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (68741124663673596732692916165919279991/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (7478496212271115486855143817715092702409/5000000000000000000000000000000000000000)

def table : Table :=
  ⟨29, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨3, (-4605170183988091/6000000000000000), 64, (23207944175799877276254101148027539490675195100669/50000000000000000000000000000000000000000000000000), (46415888351599754552508202296055078981350390201339/100000000000000000000000000000000000000000000000000)⟩, (12500000012500002306474895485862991903917515337985224013466092246217428228965300397863575423213687389113324329405946229846436134395398711052752718309/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (100000000100000018451799163886903935231340122703888255411803142491079113258947685432213027614966564639747359600776744407329223072139565681525723321219/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell086Term02
