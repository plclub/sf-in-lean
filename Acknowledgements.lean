import SFLMeta

open Verso.Genre Manual
open SFLMeta

/-!
Single shared source for the Acknowledgements section that appears in the
front matter of every volume.  Each volume's Preface includes it with
`{include 2 Acknowledgements}`, so edits here propagate to all volumes.
-/

#doc (Manual) "Acknowledgements" =>

*Leadership:* Mike Hicks and Benjamin C. Pierce are the SF-in-Lean project leads.

*Authors:*
The Lean adaptation of _Software Foundations_ was created by
Mike Hicks,
Benjamin C. Pierce,
One An,
Roger Burtonpatel,
Jonathan Chan,
Luisa Cicolini,
Harry Goldstein,
Niklas Halonen,
Chris Henson,
Kihong Heo,
Yipeng Liu,
and
Daniel Sainati,

*... with contributions from*
Michael Clarkson,
Robert Joseph,
Sati,
and
Shriya Thakur,

*... and gratitude to*
David Thrane Christiansen, for helping us understand the intricacies of Lean's Verso document preparation system.

*SF in Rocq:*
The first three volumes of _Software Foundations in Lean_ (_Logical Foundations_, _Type Systems_, and _Hoare Logic_) are adapted from the _Logical Foundations_ and _Programming Language Foundations_ volumes of the original _Software Foundations_ series, developed from 2008 to 2026 by a large team of authors and contributors led by Benjamin C. Pierce.

The original _Logical Foundations_ was written by
    Benjamin C. Pierce,
		Arthur Azevedo de Amorim,
		Chris Casinghino,
		Marco Gaboardi,
		Michael Greenberg,
		Cătălin Hriţcu,
		Vilhelm Sjöberg,
    and
		Brent Yorgey,
with contributions from
              Loris D'Antoni,
              Andrew W. Appel,
              Arthur Charguéraud,
              Michael Clarkson,
              Anthony Cowley,
              Jeffrey Foster,
              Dmitri Garbuzov,
              Olek Gierczak,
              Michael Hicks,
              Ranjit Jhala,
              Ori Lahav,
              Yishuai Li,
              Greg Morrisett,
              Jennifer Paykin,
              Mukund Raghothaman,
              Chung-chieh Shan,
              Leonid Spesivtsev,
              Caleb Stanford,
              Andrew Tolmach,
              Philip Wadler,
              Stephanie Weirich,
              Li-Yao Xia,
              and
              Steve Zdancewic.

The original _Programming Language Foundations_ was written by
  Benjamin C. Pierce,
  Arthur Azevedo de Amorim,
	Chris Casinghino,
	Marco Gaboardi,
	Michael Greenberg,
	Cătălin Hriţcu,
	Vilhelm Sjöberg,
	Andrew Tolmach, and
	Brent Yorgey
with contributions from
    Loris D'Antoni,
    Andrew W. Appel,
    Arthur Chargueraud,
    Michael Clarkson,
    Anthony Cowley,
    Jeffrey Foster,
    Dmitri Garbuzov,
    Michael Hicks,
    Ranjit Jhala,
    Ori Lahav,
    Yishuai Li,
    Greg Morrisett,
    Jennifer Paykin,
    Mukund Raghothaman,
    Chung-Chieh Shan,
    Leonid Spesivtsev,
    Caleb Stanford,
    Philip Wadler,
    Stephanie Weirich,
    Li-Yao Xia,
    and
    Steve Zdancewic.

*Funding:*
Development of the original _Software Foundations_ series in Rocq was supported, in
part, by the National Science Foundation under the NSF Expeditions grant
1521523, _The Science of Deep Specification_.
