import ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03.Batch000

import ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03.Batch001

import ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03.Batch002

import ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03.Batch003

import ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03.Batch004

import ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03.Batch005

import ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03.Batch006

import ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03.Batch007

import ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03.Batch008

import ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03.Batch009

import ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03.Batch010

import ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03.Batch011

import ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03.Batch012

import ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03.Batch013

import ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03.Batch014

import ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03.Batch015

import ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03.Batch016

import ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03.Batch017

import ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03.Batch018

import ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03.Batch019

import ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03.Batch020

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03
open CoupledFlow


def rows : List Row := Batch000.rows ++ Batch001.rows ++ Batch002.rows ++ Batch003.rows ++ Batch004.rows ++ Batch005.rows ++ Batch006.rows ++ Batch007.rows ++ Batch008.rows ++ Batch009.rows ++ Batch010.rows ++ Batch011.rows ++ Batch012.rows ++ Batch013.rows ++ Batch014.rows ++ Batch015.rows ++ Batch016.rows ++ Batch017.rows ++ Batch018.rows ++ Batch019.rows ++ Batch020.rows

theorem rows_length : rows.length=922 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked, Batch002.rows_checked, Batch003.rows_checked, Batch004.rows_checked, Batch005.rows_checked, Batch006.rows_checked, Batch007.rows_checked, Batch008.rows_checked, Batch009.rows_checked, Batch010.rows_checked, Batch011.rows_checked, Batch012.rows_checked, Batch013.rows_checked, Batch014.rows_checked, Batch015.rows_checked, Batch016.rows_checked, Batch017.rows_checked, Batch018.rows_checked, Batch019.rows_checked, Batch020.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (23065534742520556434853790474265311/312500000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (4768305265778739167859085685703854191363/2500000000000000000000000000000000000000)

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

end ForestUnimodality.BridgeFlowData.Stage99.Cell099Term03
