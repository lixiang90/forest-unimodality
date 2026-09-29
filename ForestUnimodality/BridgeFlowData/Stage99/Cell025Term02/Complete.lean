import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch000

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch001

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch002

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch003

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch004

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch005

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch006

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch007

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch008

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch009

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch010

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch011

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch012

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch013

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch014

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch015

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch016

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch017

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch018

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch019

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch020

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch021

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch022

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch023

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch024

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch025

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch026

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch027

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch028

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch029

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch030

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch031

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch032

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch033

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch034

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch035

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch036

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch037

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch038

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch039

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch040

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch041

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch042

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch043

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch044

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch045

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch046

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch047

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch048

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch049

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch050

import ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02.Batch051

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02
open CoupledFlow


def rows : List Row := Batch000.rows ++ Batch001.rows ++ Batch002.rows ++ Batch003.rows ++ Batch004.rows ++ Batch005.rows ++ Batch006.rows ++ Batch007.rows ++ Batch008.rows ++ Batch009.rows ++ Batch010.rows ++ Batch011.rows ++ Batch012.rows ++ Batch013.rows ++ Batch014.rows ++ Batch015.rows ++ Batch016.rows ++ Batch017.rows ++ Batch018.rows ++ Batch019.rows ++ Batch020.rows ++ Batch021.rows ++ Batch022.rows ++ Batch023.rows ++ Batch024.rows ++ Batch025.rows ++ Batch026.rows ++ Batch027.rows ++ Batch028.rows ++ Batch029.rows ++ Batch030.rows ++ Batch031.rows ++ Batch032.rows ++ Batch033.rows ++ Batch034.rows ++ Batch035.rows ++ Batch036.rows ++ Batch037.rows ++ Batch038.rows ++ Batch039.rows ++ Batch040.rows ++ Batch041.rows ++ Batch042.rows ++ Batch043.rows ++ Batch044.rows ++ Batch045.rows ++ Batch046.rows ++ Batch047.rows ++ Batch048.rows ++ Batch049.rows ++ Batch050.rows ++ Batch051.rows

theorem rows_length : rows.length=922 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked, Batch002.rows_checked, Batch003.rows_checked, Batch004.rows_checked, Batch005.rows_checked, Batch006.rows_checked, Batch007.rows_checked, Batch008.rows_checked, Batch009.rows_checked, Batch010.rows_checked, Batch011.rows_checked, Batch012.rows_checked, Batch013.rows_checked, Batch014.rows_checked, Batch015.rows_checked, Batch016.rows_checked, Batch017.rows_checked, Batch018.rows_checked, Batch019.rows_checked, Batch020.rows_checked, Batch021.rows_checked, Batch022.rows_checked, Batch023.rows_checked, Batch024.rows_checked, Batch025.rows_checked, Batch026.rows_checked, Batch027.rows_checked, Batch028.rows_checked, Batch029.rows_checked, Batch030.rows_checked, Batch031.rows_checked, Batch032.rows_checked, Batch033.rows_checked, Batch034.rows_checked, Batch035.rows_checked, Batch036.rows_checked, Batch037.rows_checked, Batch038.rows_checked, Batch039.rows_checked, Batch040.rows_checked, Batch041.rows_checked, Batch042.rows_checked, Batch043.rows_checked, Batch044.rows_checked, Batch045.rows_checked, Batch046.rows_checked, Batch047.rows_checked, Batch048.rows_checked, Batch049.rows_checked, Batch050.rows_checked, Batch051.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (1596577502255158408746719446470440749/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (15802469135802469135802469135802469135803/10000000000000000000000000000000000000000)

def table : Table :=
  ⟨922, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨5, (-230258509299404568401799145468436420759/250000000000000000000000000000000000000), 64, (7962143411069945015405046101755040869788897403763/20000000000000000000000000000000000000000000000000), (622042453989839454328519226699612567952257609669/1562500000000000000000000000000000000000000000000)⟩, (32000000000000000000000000000000000000710495272240063703661501724185746899666863008710998298959763065562951879942684547980098245063320009185464632006650066596269794341550849393851272371043532172750703272723975920673178441511676488682236133515043/3200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (93132257461547851562500000000000000002067813394370263913739231218244772610997728574269344434312006019187544564473259181748127329748695823343833544256015581175939518035323179987782841909474488469517436727413007496996153119594179741088239349/9313225746154785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage99.Cell025Term02
