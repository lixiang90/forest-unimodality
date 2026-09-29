import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch000

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch001

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch002

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch003

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch004

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch005

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch006

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch007

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch008

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch009

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch010

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch011

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch012

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch013

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch014

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch015

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch016

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch017

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch018

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch019

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch020

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch021

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch022

import ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01.Batch023

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01
open CoupledFlow


def rows : List Row := Batch000.rows ++ Batch001.rows ++ Batch002.rows ++ Batch003.rows ++ Batch004.rows ++ Batch005.rows ++ Batch006.rows ++ Batch007.rows ++ Batch008.rows ++ Batch009.rows ++ Batch010.rows ++ Batch011.rows ++ Batch012.rows ++ Batch013.rows ++ Batch014.rows ++ Batch015.rows ++ Batch016.rows ++ Batch017.rows ++ Batch018.rows ++ Batch019.rows ++ Batch020.rows ++ Batch021.rows ++ Batch022.rows ++ Batch023.rows

theorem rows_length : rows.length=380 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked, Batch002.rows_checked, Batch003.rows_checked, Batch004.rows_checked, Batch005.rows_checked, Batch006.rows_checked, Batch007.rows_checked, Batch008.rows_checked, Batch009.rows_checked, Batch010.rows_checked, Batch011.rows_checked, Batch012.rows_checked, Batch013.rows_checked, Batch014.rows_checked, Batch015.rows_checked, Batch016.rows_checked, Batch017.rows_checked, Batch018.rows_checked, Batch019.rows_checked, Batch020.rows_checked, Batch021.rows_checked, Batch022.rows_checked, Batch023.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (140593039314509069952983973733286239641/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (419011646389308810274305919600890963771/312500000000000000000000000000000000000)

def table : Table :=
  ⟨380, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨2, (-1897119984885881302039978339220015071/2000000000000000000000000000000000000), 64, (9682458365518542212948163499455999027223237601453/25000000000000000000000000000000000000000000000000), (38729833462074168851792653997823996108892950405813/100000000000000000000000000000000000000000000000000)⟩, (93750000000000000000000000000000000002729162359335289963601123617504626915248598599164488467711209/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (1500000000000000000000000000000000000043666597749442099084542126217777615951973225578849601384190969/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell072Term01
