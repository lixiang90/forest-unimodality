import ForestUnimodality.BridgeFlowData.Stage80.Cell099Term01.Batch000

import ForestUnimodality.BridgeFlowData.Stage80.Cell099Term01.Batch001

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell099Term01
open CoupledFlow


def rows : List Row := Batch000.rows ++ Batch001.rows

theorem rows_length : rows.length=20 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (900626142447515112517544016768907619/156250000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (7909348131621341223979421992676636309357/5000000000000000000000000000000000000000)

def table : Table :=
  ⟨20, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨3, (-11160864579549677/15000000000000000), 64, (47518188206096125976649781335705885045911711032081/100000000000000000000000000000000000000000000000000), (23759094103048062988324890667852942522955855516041/50000000000000000000000000000000000000000000000000)⟩, (107295033566574850268765746180298608947185042692925574094027254868149380408962290418616777464165524869237622824982753573370447984891417437697075387441/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (13411879195821856283595718272537326118398130336616543503582303098379773501988506686140067227562257883517955715112520165446876967577357812504855256921/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell099Term01
