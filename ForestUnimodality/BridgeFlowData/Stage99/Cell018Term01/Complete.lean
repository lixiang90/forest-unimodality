import ForestUnimodality.BridgeFlowData.Stage99.Cell018Term01.Batch000

import ForestUnimodality.BridgeFlowData.Stage99.Cell018Term01.Batch001

import ForestUnimodality.BridgeFlowData.Stage99.Cell018Term01.Batch002

import ForestUnimodality.BridgeFlowData.Stage99.Cell018Term01.Batch003

import ForestUnimodality.BridgeFlowData.Stage99.Cell018Term01.Batch004

import ForestUnimodality.BridgeFlowData.Stage99.Cell018Term01.Batch005

import ForestUnimodality.BridgeFlowData.Stage99.Cell018Term01.Batch006

import ForestUnimodality.BridgeFlowData.Stage99.Cell018Term01.Batch007

import ForestUnimodality.BridgeFlowData.Stage99.Cell018Term01.Batch008

import ForestUnimodality.BridgeFlowData.Stage99.Cell018Term01.Batch009

import ForestUnimodality.BridgeFlowData.Stage99.Cell018Term01.Batch010

import ForestUnimodality.BridgeFlowData.Stage99.Cell018Term01.Batch011

import ForestUnimodality.BridgeFlowData.Stage99.Cell018Term01.Batch012

import ForestUnimodality.BridgeFlowData.Stage99.Cell018Term01.Batch013

import ForestUnimodality.BridgeFlowData.Stage99.Cell018Term01.Batch014

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell018Term01
open CoupledFlow


def rows : List Row := Batch000.rows ++ Batch001.rows ++ Batch002.rows ++ Batch003.rows ++ Batch004.rows ++ Batch005.rows ++ Batch006.rows ++ Batch007.rows ++ Batch008.rows ++ Batch009.rows ++ Batch010.rows ++ Batch011.rows ++ Batch012.rows ++ Batch013.rows ++ Batch014.rows

theorem rows_length : rows.length=691 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked, Batch002.rows_checked, Batch003.rows_checked, Batch004.rows_checked, Batch005.rows_checked, Batch006.rows_checked, Batch007.rows_checked, Batch008.rows_checked, Batch009.rows_checked, Batch010.rows_checked, Batch011.rows_checked, Batch012.rows_checked, Batch013.rows_checked, Batch014.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (17856946089143483022380051547238789/5000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (6275124951941560938100730488273740868897/5000000000000000000000000000000000000000)

def table : Table :=
  ⟨691, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨7, (-49341109135586693228956959743236375877/50000000000000000000000000000000000000), 64, (37275937203149401661724906094730409920895927412083/100000000000000000000000000000000000000000000000000), (9318984300787350415431226523682602480223981853021/25000000000000000000000000000000000000000000000000)⟩, (100000000000000000000000000000000000002330446588619065332045860742672633681643958832197994081726350599608529328524150728069010002569974456812618516904972764241842308067031577905120924734680501317587951233531250794648375056004072231499291669512027637845363156424624013392294240521968875245604606842024342054124978332142047498581992005244386520185627/100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (6103515625000000000000000000000000000142239171669790295569630055109040850855001965777944713347704310067687626419443265542131597855059217525968482039661015777411349174058375595127226940421740567077261398831259871040983726709930059768904062484515297235025529735672857516509396055335720161382848669907424267063154530223563879610735393680905579541/6103515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage99.Cell018Term01
