import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch000

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch001

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch002

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch003

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch004

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch005

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch006

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch007

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch008

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch009

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch010

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch011

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch012

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch013

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch014

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch015

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch016

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch017

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch018

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch019

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch020

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch021

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch022

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch023

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch024

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch025

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch026

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch027

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch028

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch029

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch030

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch031

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch032

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch033

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch034

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch035

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch036

import ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03.Batch037

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03
open CoupledFlow


def rows : List Row := Batch000.rows ++ Batch001.rows ++ Batch002.rows ++ Batch003.rows ++ Batch004.rows ++ Batch005.rows ++ Batch006.rows ++ Batch007.rows ++ Batch008.rows ++ Batch009.rows ++ Batch010.rows ++ Batch011.rows ++ Batch012.rows ++ Batch013.rows ++ Batch014.rows ++ Batch015.rows ++ Batch016.rows ++ Batch017.rows ++ Batch018.rows ++ Batch019.rows ++ Batch020.rows ++ Batch021.rows ++ Batch022.rows ++ Batch023.rows ++ Batch024.rows ++ Batch025.rows ++ Batch026.rows ++ Batch027.rows ++ Batch028.rows ++ Batch029.rows ++ Batch030.rows ++ Batch031.rows ++ Batch032.rows ++ Batch033.rows ++ Batch034.rows ++ Batch035.rows ++ Batch036.rows ++ Batch037.rows

theorem rows_length : rows.length=600 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked, Batch002.rows_checked, Batch003.rows_checked, Batch004.rows_checked, Batch005.rows_checked, Batch006.rows_checked, Batch007.rows_checked, Batch008.rows_checked, Batch009.rows_checked, Batch010.rows_checked, Batch011.rows_checked, Batch012.rows_checked, Batch013.rows_checked, Batch014.rows_checked, Batch015.rows_checked, Batch016.rows_checked, Batch017.rows_checked, Batch018.rows_checked, Batch019.rows_checked, Batch020.rows_checked, Batch021.rows_checked, Batch022.rows_checked, Batch023.rows_checked, Batch024.rows_checked, Batch025.rows_checked, Batch026.rows_checked, Batch027.rows_checked, Batch028.rows_checked, Batch029.rows_checked, Batch030.rows_checked, Batch031.rows_checked, Batch032.rows_checked, Batch033.rows_checked, Batch034.rows_checked, Batch035.rows_checked, Batch036.rows_checked, Batch037.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (20150563014137604377898783081827848131/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (16207882837226857910679712477136400062821/10000000000000000000000000000000000000000)

def table : Table :=
  ⟨600, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨3, (-59914645471079819868704471522850815513/60000000000000000000000000000000000000), 64, (4605039373300483257224778541974759027437406487217/12500000000000000000000000000000000000000000000000), (36840314986403866057798228335798072219499251897737/100000000000000000000000000000000000000000000000000)⟩, (97656250000000000000000000000000000002597814745014753494723315905157561892807411726594318829266784716510931828011077048260729532569505846228247313/1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (50000000000000000000000000000000000001330081149451625415723230103297948823321914037823571110152898755664273356198610395875778832610752934758824094553/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage99.Cell047Term03
