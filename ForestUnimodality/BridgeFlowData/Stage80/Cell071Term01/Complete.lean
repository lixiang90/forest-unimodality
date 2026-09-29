import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch000

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch001

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch002

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch003

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch004

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch005

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch006

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch007

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch008

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch009

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch010

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch011

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch012

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch013

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch014

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch015

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch016

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch017

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch018

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch019

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch020

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch021

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch022

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch023

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch024

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch025

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch026

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch027

import ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01.Batch028

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01
open CoupledFlow


def rows : List Row := Batch000.rows ++ Batch001.rows ++ Batch002.rows ++ Batch003.rows ++ Batch004.rows ++ Batch005.rows ++ Batch006.rows ++ Batch007.rows ++ Batch008.rows ++ Batch009.rows ++ Batch010.rows ++ Batch011.rows ++ Batch012.rows ++ Batch013.rows ++ Batch014.rows ++ Batch015.rows ++ Batch016.rows ++ Batch017.rows ++ Batch018.rows ++ Batch019.rows ++ Batch020.rows ++ Batch021.rows ++ Batch022.rows ++ Batch023.rows ++ Batch024.rows ++ Batch025.rows ++ Batch026.rows ++ Batch027.rows ++ Batch028.rows

theorem rows_length : rows.length=461 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked, Batch002.rows_checked, Batch003.rows_checked, Batch004.rows_checked, Batch005.rows_checked, Batch006.rows_checked, Batch007.rows_checked, Batch008.rows_checked, Batch009.rows_checked, Batch010.rows_checked, Batch011.rows_checked, Batch012.rows_checked, Batch013.rows_checked, Batch014.rows_checked, Batch015.rows_checked, Batch016.rows_checked, Batch017.rows_checked, Batch018.rows_checked, Batch019.rows_checked, Batch020.rows_checked, Batch021.rows_checked, Batch022.rows_checked, Batch023.rows_checked, Batch024.rows_checked, Batch025.rows_checked, Batch026.rows_checked, Batch027.rows_checked, Batch028.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (16902216556272161339476692735932521661/2500000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (14492753578733700122985762027729792555853/10000000000000000000000000000000000000000)

def table : Table :=
  ⟨461, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨3, (-115129254649702284200899572734218210379/150000000000000000000000000000000000000), 64, (2900993021007986807756297719324654110364998293547/6250000000000000000000000000000000000000000000000), (46415888336127788924100763509194465765839972696753/100000000000000000000000000000000000000000000000000)⟩, (24414062500000000000000000000000000000515173062225636650771337541477310479717165710197941378699459979947267739157031662094680447803933706123378323/244140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (100000000000000000000000000000000000002110148862882671025629494221056341605621068800456636845537790779548945135767508132969913684394875304283329749777/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell071Term01
