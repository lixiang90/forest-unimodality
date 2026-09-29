import ForestUnimodality.BridgeFlowData.Stage130.Cell011Term01.Batch000

import ForestUnimodality.BridgeFlowData.Stage130.Cell011Term01.Batch001

import ForestUnimodality.BridgeFlowData.Stage130.Cell011Term01.Batch002

import ForestUnimodality.BridgeFlowData.Stage130.Cell011Term01.Batch003

import ForestUnimodality.BridgeFlowData.Stage130.Cell011Term01.Batch004

import ForestUnimodality.BridgeFlowData.Stage130.Cell011Term01.Batch005

import ForestUnimodality.BridgeFlowData.Stage130.Cell011Term01.Batch006

import ForestUnimodality.BridgeFlowData.Stage130.Cell011Term01.Batch007

import ForestUnimodality.BridgeFlowData.Stage130.Cell011Term01.Batch008

import ForestUnimodality.BridgeFlowData.Stage130.Cell011Term01.Batch009

import ForestUnimodality.BridgeFlowData.Stage130.Cell011Term01.Batch010

import ForestUnimodality.BridgeFlowData.Stage130.Cell011Term01.Batch011

import ForestUnimodality.BridgeFlowData.Stage130.Cell011Term01.Batch012

import ForestUnimodality.BridgeFlowData.Stage130.Cell011Term01.Batch013

import ForestUnimodality.BridgeFlowData.Stage130.Cell011Term01.Batch014

import ForestUnimodality.BridgeFlowData.Stage130.Cell011Term01.Batch015

import ForestUnimodality.BridgeFlowData.Stage130.Cell011Term01.Batch016

import ForestUnimodality.BridgeFlowData.Stage130.Cell011Term01.Batch017

import ForestUnimodality.BridgeFlowData.Stage130.Cell011Term01.Batch018

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell011Term01
open CoupledFlow


def rows : List Row := Batch000.rows ++ Batch001.rows ++ Batch002.rows ++ Batch003.rows ++ Batch004.rows ++ Batch005.rows ++ Batch006.rows ++ Batch007.rows ++ Batch008.rows ++ Batch009.rows ++ Batch010.rows ++ Batch011.rows ++ Batch012.rows ++ Batch013.rows ++ Batch014.rows ++ Batch015.rows ++ Batch016.rows ++ Batch017.rows ++ Batch018.rows

theorem rows_length : rows.length=300 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked, Batch002.rows_checked, Batch003.rows_checked, Batch004.rows_checked, Batch005.rows_checked, Batch006.rows_checked, Batch007.rows_checked, Batch008.rows_checked, Batch009.rows_checked, Batch010.rows_checked, Batch011.rows_checked, Batch012.rows_checked, Batch013.rows_checked, Batch014.rows_checked, Batch015.rows_checked, Batch016.rows_checked, Batch017.rows_checked, Batch018.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (1239447000244652502663412166497148107/625000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (2328027681660899653979238754325259515571/2500000000000000000000000000000000000000)

def table : Table :=
  ⟨300, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨3, (-59914645471079819868704471522850815513/60000000000000000000000000000000000000), 64, (4605039373300483257224778541974759027437406487217/12500000000000000000000000000000000000000000000000), (36840314986403866057798228335798072219499251897737/100000000000000000000000000000000000000000000000000)⟩, (97656250000000000000000000000000000002597814745014753494723315905157561892807411726594318829266784716510931828011077048260729532569505846228247313/1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (50000000000000000000000000000000000001330081149451625415723230103297948823321914037823571110152898755664273356198610395875778832610752934758824094553/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage130.Cell011Term01
