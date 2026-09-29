import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch000

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch001

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch002

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch003

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch004

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch005

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch006

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch007

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch008

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch009

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch010

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch011

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch012

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch013

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch014

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch015

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch016

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch017

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch018

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch019

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch020

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch021

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch022

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch023

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch024

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch025

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch026

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch027

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch028

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch029

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch030

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch031

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch032

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch033

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch034

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch035

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch036

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch037

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch038

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch039

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch040

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch041

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch042

import ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01.Batch043

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01
open CoupledFlow


def rows : List Row := Batch000.rows ++ Batch001.rows ++ Batch002.rows ++ Batch003.rows ++ Batch004.rows ++ Batch005.rows ++ Batch006.rows ++ Batch007.rows ++ Batch008.rows ++ Batch009.rows ++ Batch010.rows ++ Batch011.rows ++ Batch012.rows ++ Batch013.rows ++ Batch014.rows ++ Batch015.rows ++ Batch016.rows ++ Batch017.rows ++ Batch018.rows ++ Batch019.rows ++ Batch020.rows ++ Batch021.rows ++ Batch022.rows ++ Batch023.rows ++ Batch024.rows ++ Batch025.rows ++ Batch026.rows ++ Batch027.rows ++ Batch028.rows ++ Batch029.rows ++ Batch030.rows ++ Batch031.rows ++ Batch032.rows ++ Batch033.rows ++ Batch034.rows ++ Batch035.rows ++ Batch036.rows ++ Batch037.rows ++ Batch038.rows ++ Batch039.rows ++ Batch040.rows ++ Batch041.rows ++ Batch042.rows ++ Batch043.rows

theorem rows_length : rows.length=691 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked, Batch002.rows_checked, Batch003.rows_checked, Batch004.rows_checked, Batch005.rows_checked, Batch006.rows_checked, Batch007.rows_checked, Batch008.rows_checked, Batch009.rows_checked, Batch010.rows_checked, Batch011.rows_checked, Batch012.rows_checked, Batch013.rows_checked, Batch014.rows_checked, Batch015.rows_checked, Batch016.rows_checked, Batch017.rows_checked, Batch018.rows_checked, Batch019.rows_checked, Batch020.rows_checked, Batch021.rows_checked, Batch022.rows_checked, Batch023.rows_checked, Batch024.rows_checked, Batch025.rows_checked, Batch026.rows_checked, Batch027.rows_checked, Batch028.rows_checked, Batch029.rows_checked, Batch030.rows_checked, Batch031.rows_checked, Batch032.rows_checked, Batch033.rows_checked, Batch034.rows_checked, Batch035.rows_checked, Batch036.rows_checked, Batch037.rows_checked, Batch038.rows_checked, Batch039.rows_checked, Batch040.rows_checked, Batch041.rows_checked, Batch042.rows_checked, Batch043.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (34314938212405449829931172362152203/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (3449231544469639707734945830183925422021/5000000000000000000000000000000000000000)

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

end ForestUnimodality.BridgeFlowData.Stage130.Cell005Term01
