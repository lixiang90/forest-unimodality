import ForestUnimodality.BridgeFlowData.Stage80.Cell191Term03.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell191Term03
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=16 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (35020070298531286462100464091028127443/5000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (3034954600000944445353404824581609106211/2000000000000000000000000000000000000000)

def table : Table :=
  ⟨16, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨2, (-60353921716278761/80000000000000000), 64, (47028140873954081515559050298230393357184275456201/100000000000000000000000000000000000000000000000000), (23514070436977040757779525149115196678592137728101/50000000000000000000000000000000000000000000000000)⟩, (2211646034060470561965982989088874657160037273811802049883840392817471151126763667157272086669352401/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (552911508515117640491495747272218664290009318452974026541397075245125567306840031985996613805066201/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell191Term03
