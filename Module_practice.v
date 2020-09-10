(** Modules *)

(* Examples are taken from: The Module System — Coq 8.12.0 documentation *)

(** Defining a simple module interactively *)

Module M.


Definition T := nat.
Definition x := 0.

Definition y : bool.
exact true.
Defined.

End M.

(** Defining a simple module type interactively *)

Module Type SIG.
Parameter T : Set.
Parameter x : T.
End SIG.


(** Creating a new Module from an existing module *)
(* non interactive command *)

(* -- omitting some items through opaque constraint -- *)

(* Module ident1 : Module Type := ident2 *)
Module N : SIG with Definition T := nat := M.

Print N.T.

Print N.x.

(* Following command will fail as N's module type SIG has 
been ascribed with colon - opaque ascription, that hides all 
details of the module not exposed by the signature
thus it doesn't include y *)

Fail Print N.y. 

(* -- not ommiting through transparent constraint -- *)

(* If we just want to be sure that our implementation satisfies 
a given module type without restricting the interface, we can 
use the transparent constraint (<:) *)

Module P <: SIG := M.

Print P.y.

(** Creating a functor (a module with parameters) *)

Module Two (X Y: SIG).
Definition T := (X.T * Y.T)%type.
Definition x := (X.x, Y.x).
End Two.

(* applying it to above modules and doing some computations*)

Module Q := Two M N.
Eval compute in (fst Q.x + snd Q.x).


(** Importing Modules *)

Module Mod.
Definition T:=nat.
Check T.
End Mod.

Check Mod.T.

Fail Check T.

Import Mod.

(* Importing basic modules makes its components available 
by their short names. *)
Check T.

(* Declarations made with the local attribute are never 
imported by the Import command. Such declarations are only 
accessible through their fully qualified name.*)
Module A.
Module B.
Local Definition T := nat.
End B.
End A.

Import A.

Fail Check B.T.

Check A.B.T.

(* Note that, to import a module from a different file, 
either file containing the module needs to be compiled 
into .vo file or file need to be loaded with Load command to 
insert its content. .vo files are loaded with Require Imoprt/ Export
command *) 

(* Using coq standard library *)

(* Similarly Require Import can be used to load coq standard library
files that are modules possibly containing submodules *)

Require Import Coq.Arith.Arith.

