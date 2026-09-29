import ForestUnimodality.LowActivityFlowData.Cell010.Batch000

import ForestUnimodality.LowActivityFlowData.Cell010.Batch001

import ForestUnimodality.LowActivityFlowData.Cell010.Batch002

import ForestUnimodality.LowActivityFlowData.Cell010.Batch003

import ForestUnimodality.LowActivityFlowData.Cell010.Batch004

import ForestUnimodality.LowActivityFlowData.Cell010.Batch005

import ForestUnimodality.LowActivityFlowData.Cell010.Batch006

import ForestUnimodality.LowActivityFlowData.Cell010.Batch007

import ForestUnimodality.LowActivityFlowData.Cell010.Batch008

import ForestUnimodality.LowActivityFlowData.Cell010.Batch009

import ForestUnimodality.LowActivityFlowData.Cell010.Batch010

import ForestUnimodality.LowActivityFlowData.Cell010.Batch011

import ForestUnimodality.LowActivityFlowData.Cell010.Batch012

import ForestUnimodality.LowActivityFlowData.Cell010.Batch013

import ForestUnimodality.LowActivityFlowData.Cell010.Batch014

import ForestUnimodality.LowActivityFlowData.Cell010.Batch015

import ForestUnimodality.LowActivityFlowData.Cell010.Batch016

import ForestUnimodality.LowActivityFlowData.Cell010.Batch017

import ForestUnimodality.LowActivityFlowData.Cell010.Batch018

import ForestUnimodality.LowActivityFlowData.Cell010.Batch019

import ForestUnimodality.LowActivityFlowData.Cell010.Batch020

import ForestUnimodality.LowActivityFlowData.Cell010.Batch021

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.LowActivityFlowData.Cell010
open LowActivityFlow


def rows : List Row := Batch000.rows ++ Batch001.rows ++ Batch002.rows ++ Batch003.rows ++ Batch004.rows ++ Batch005.rows ++ Batch006.rows ++ Batch007.rows ++ Batch008.rows ++ Batch009.rows ++ Batch010.rows ++ Batch011.rows ++ Batch012.rows ++ Batch013.rows ++ Batch014.rows ++ Batch015.rows ++ Batch016.rows ++ Batch017.rows ++ Batch018.rows ++ Batch019.rows ++ Batch020.rows ++ Batch021.rows

theorem rows_length : rows.length=691 := rfl

theorem rows_checked : rows.all (fun r=>r.check b beta)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked, Batch002.rows_checked, Batch003.rows_checked, Batch004.rows_checked, Batch005.rows_checked, Batch006.rows_checked, Batch007.rows_checked, Batch008.rows_checked, Batch009.rows_checked, Batch010.rows_checked, Batch011.rows_checked, Batch012.rows_checked, Batch013.rows_checked, Batch014.rows_checked, Batch015.rows_checked, Batch016.rows_checked, Batch017.rows_checked, Batch018.rows_checked, Batch019.rows_checked, Batch020.rows_checked, Batch021.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (2234728022017722308199641376151313/625000000000000000000000000000000000000)

def table : Table :=
  ⟨691, qa, b, beta, retention, rate, timeAt, lowerAt, rowAt, ⟨7, (-49341109135586693228956959743236375877/50000000000000000000000000000000000000), 64, (37275937203149401661724906094730409920895927412083/100000000000000000000000000000000000000000000000000), (9318984300787350415431226523682602480223981853021/25000000000000000000000000000000000000000000000000)⟩, (100000000000000000000000000000000000002330446588619065332045860742672633681643958832197994081726350599608529328524150728069010002569974456812618516904972764241842308067031577905120924734680501317587951233531250794648375056004072231499291669512027637845363156424624013392294240521968875245604606842024342054124978332142047498581992005244386520185627/100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (6103515625000000000000000000000000000142239171669790295569630055109040850855001965777944713347704310067687626419443265542131597855059217525968482039661015777411349174058375595127226940421740567077261398831259871040983726709930059768904062484515297235025529735672857516509396055335720161382848669907424267063154530223563879610735393680905579541/6103515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.LowActivityFlowData.Cell010
