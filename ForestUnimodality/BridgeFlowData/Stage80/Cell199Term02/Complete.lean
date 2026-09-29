import ForestUnimodality.BridgeFlowData.Stage80.Cell199Term02.Batch000

import ForestUnimodality.BridgeFlowData.Stage80.Cell199Term02.Batch001

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell199Term02
open CoupledFlow


def rows : List Row := Batch000.rows ++ Batch001.rows

theorem rows_length : rows.length=25 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (10020315124319955549875804911928160469/5000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (17019402072870561143738354295239216158867/10000000000000000000000000000000000000000)

def table : Table :=
  ⟨25, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨2, (-1897119984885881302039978339220015071/2000000000000000000000000000000000000), 64, (9682458365518542212948163499455999027223237601453/25000000000000000000000000000000000000000000000000), (38729833462074168851792653997823996108892950405813/100000000000000000000000000000000000000000000000000)⟩, (93750000000000000000000000000000000002729162359335289963601123617504626915248598599164488467711209/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (1500000000000000000000000000000000000043666597749442099084542126217777615951973225578849601384190969/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell199Term02
