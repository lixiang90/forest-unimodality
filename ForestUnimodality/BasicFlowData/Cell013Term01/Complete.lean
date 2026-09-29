import ForestUnimodality.BasicFlowData.Cell013Term01.Batch000

import ForestUnimodality.BasicFlowData.Cell013Term01.Batch001

import ForestUnimodality.BasicFlowData.Cell013Term01.Batch002

import ForestUnimodality.BasicFlowData.Cell013Term01.Batch003

import ForestUnimodality.BasicFlowData.Cell013Term01.Batch004

import ForestUnimodality.BasicFlowData.Cell013Term01.Batch005

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BasicFlowData.Cell013Term01
open BasicFlow


def rows : List Row := Batch000.rows ++ Batch001.rows ++ Batch002.rows ++ Batch003.rows ++ Batch004.rows ++ Batch005.rows

theorem rows_length : rows.length=190 := rfl

theorem rows_checked : rows.all (fun r=>r.check b beta)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked, Batch002.rows_checked, Batch003.rows_checked, Batch004.rows_checked, Batch005.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (12197908714075223828241954141248299473/1000000000000000000000000000000000000000)

def table : Table :=
  ⟨190, qa, b, beta, retention, rate, timeAt, lowerAt, rowAt, ⟨2, (-1897119984885881302039978339220015071/2000000000000000000000000000000000000), 64, (9682458365518542212948163499455999027223237601453/25000000000000000000000000000000000000000000000000), (38729833462074168851792653997823996108892950405813/100000000000000000000000000000000000000000000000000)⟩, (93750000000000000000000000000000000002729162359335289963601123617504626915248598599164488467711209/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (1500000000000000000000000000000000000043666597749442099084542126217777615951973225578849601384190969/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

theorem header_checked : table.headerCheck=true := by decide +kernel

theorem connections_checked : (List.range table.n).all table.connectionCheck=true := by decide +kernel

theorem table_rows_checked : (List.range table.n).all (fun i=>(table.row i).check table.b table.beta)=true := by

  apply List.all_eq_true.mpr
  intro i hi
  apply check_getD rows Batch000.row000 b beta rows_checked i
  rw [rows_length]
  exact List.mem_range.mp hi

#print axioms header_checked

#print axioms connections_checked

#print axioms table_rows_checked

end ForestUnimodality.BasicFlowData.Cell013Term01
