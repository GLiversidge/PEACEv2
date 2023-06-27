/* This file contains all the code needed to initialise PEACEv2.

    Written by Georgina Liversidge under the supervision of Marston Conder,
    for her PhD thesis in Mathematics at the University of Auckland, 2023.

    PEACEv2 takes a group G and set of group elements Hgens and returns 
    a list L of information which is required for proveWrd.
    L contains the following information:
    colLets: the generator letter corresponding to each column of CT
    CT: the Coset table of H in G
    auxTab: 
        auxTab[cos][1] gives the row of CT which corresponds to the coset cos, 
            or 0 if the row has been removed
        auxTab[cos][2] the equivalent coset if cos is redundant, or 0 if
            cos is active
        auxTab[cos][3] gives the coset from which cos was defined
        auxTab[cos][4] give the column (thus the generator) used in the 
            definition of cos
    PT: PT[cos][col] gives the way each entry in that position of the coset table
        was obtained
    POL1: POL1[cos] has gives the way the redundancy of cos was obtained
    PT2: each element of PT[cos,col] is a proof word for cos*col=cos2 for some 
        cos2, which was at some point the value of CT[cos,col]
    POL2: POL2[cos] gives the proof word for cos=cos2, where cos2 is the
        equivalent coset to cos when cos was made redundant. Not that cos2 
        may now also be redundant.
*/
/*initialise universal variables*/
    maxrow:=50000;//maximum row of the coset table
    llimit:=10^6;//maximum number of loops allowed in enumeration.
    alph:="abcdefghijklmnopqrstuvwxyz";//lower case letters
    ALPH:="ABCDEFGHIJKLMNOPQRSTUVWXYZ";//upper case letters
    digs:="1234567890";//digits as strings
    ws:=[" ","\t", "\n","\r"];//white space characters
/*universal variables initialised*/

/*PEACEv2 Utility functions*/
    /*CTprint (coset table print)
        since we do not rename cosets when they are removed from the coset table,
        the coset number do not match the row numbers. This procedure prints the 
        coset name before each row.
        Note this is not used in the code but is very useful for debugging*/
    CTprint:=procedure(CT, auxTab)
        for cos in [1..#auxTab] do
            if auxTab[cos][1] gt 0 then//not redundant
                print cos, CT[auxTab[cos][1]];
            end if;
        end for;
    end procedure;

    /*caseConv (case conversion)
        takes a letter (let) and returns the corresponding lower/upper 
        case letter with caseConv(a)=A caseConv(A)=a*/
    caseConv:=function(let)
        if let in ALPH then
            return alph[Index(ALPH,let)];
        elif let in alph then
            return ALPH[Index(alph,let)];
        else//error
            print "error in caseConv: let not in alphabet:", let;
            read str;
            return "";
        end if;
    end function;

    /*isInvGen (is inverse generator?)
        returns true if gen1 is the inverse of gen2, false otherwise
        gen1, gen2 should be given as strings*/
    isInvGen:=function(gen1, gen2)
        if gen1 in alph and gen2 in ALPH then
            i:=Index(alph,gen1);
            return gen2 eq ALPH[i];
        elif gen1 in ALPH and gen2 in alph then
            i:=Index(ALPH,gen1);
            return gen2 eq alph[i];
        else
            return false;
        end if;
    end function;

    /*invWrd (invert word)
        gives the inverse of wrd as a string. 
        wrd should be a string of characters from alph and ALPH
        invWrd("aBc")="CbA"*/
    invWrd:=function(wrd)
        wrd2:="";//the inverse wrd
        i:=#wrd;//index in wrd
        while i ge 1 do
            if wrd[i] in alph then
                j:=Index(alph,wrd[i]);
                wrd2 cat:=ALPH[j];
            elif wrd[i] in ALPH then
                j:=Index(ALPH,wrd[i]);
                wrd2 cat:=alph[j];
            else //error
                print "unknown character in invWrd:", wrd[i];
                wrd2 cat:=wrd[i];
                read str;
            end if;
            i-:=1;
        end while;
        return wrd2;
    end function;

    /*invPItem (inverse proof item)
        gives the inverse of a proof word item. 
        there are three types of proof items:
        1. generator of G
        2. relation of G
        3. generator of H*/
    invPItem:=function(str)
        if #str eq 1 then//type 1
            return caseConv(str);
        end if;
        str2:=str[1];//return value, first character is the bracket
        i:=#str-1;//index in str
        while i ge 2 do
            str2 cat:=caseConv(str[i]);//add inverse letter
            i-:=1;
        end while;
        str2 cat:=str[#str];//add end bracket
        return str2;
    end function;
    
    /*isInvPItem (inverse proof item)
        returns true if str1 is the inverse of str2, false otherwise*/
    isInvPItem:=function(str1, str2)
        if #str1 ne #str2 then//can't be inverse
            return false;
        end if;
        if #str1 eq 1 then//type 1 item or "="
            if str1 eq "=" then
                if str2 eq "=" then
                    return true;
                else
                    return false;
                end if;
            elif str2 eq "=" then 
                return false;
            else
                return isInvGen(str1,str2);
            end if;
        end if;
        //must be type 2 or 3 if here
        if str1[1] ne str2[1] then//different types
            return false;
        end if;
        i:=2;//index in str1
        while i lt #str1 do
            if not(isInvGen(str1[i], str2[#str1+1-i])) then
                return false;
            end if;
            i+:=1;
        end while;
        return true;
    end function;

    /*readWrd (read word)
        takes a string (wrd) and converts it into a string of letters only 
        characters for example "(ab)^3" becomes "ababab"
        it is easier for the user to enter (ab)^3, but the algorithm uses 
        "ababab"
        potentially readWrd could be altered to allow different formats of 
        entry if required*/
    forward readWrd;
    readWrd:=function(wrd)
        wrd2:="";//holds new word
        i:=1;//index in wrd
        while i le #wrd do
            if wrd[i] eq "(" then
                j:=i+1;//2nd index in wrd
                ct:=1;//count of open brackets
                cflag:=false;//flags if this is a commutator
                //find the corresponding ")"
                while ct gt 0 do
                    if wrd[j] eq "(" then//new open bracket
                        ct+:=1;
                    elif wrd[j] eq ")" then//bracket closed
                        ct-:=1;
                    elif wrd[j] eq "," and ct eq 1 then//commutator
                        cflag:=true;
                        break;
                    end if;
                    j+:=1;
                end while;
                if cflag then
                    k:=j+1;//3rd index in wrd
                    while ct gt 0 do
                        if wrd[k] eq "(" then//new open bracket
                            ct+:=1;
                        elif wrd[k] eq ")" then//bracket closed
                            ct-:=1;
                        elif wrd[k] eq "," and ct eq 1 then//error
                            print "double commutator not supported.";
                            print "wrd=", wrd;
                            return [];
                        end if;
                        k+:=1;
                    end while;
                    wrd4:=readWrd(wrd[(i+1)..(j-1)]);
                    wrd5:=readWrd(wrd[(j+1)..(k-2)]);
                    wrd3:=wrd4 cat wrd5 cat invWrd(wrd4) cat invWrd(wrd5);
                    j:=k;
                else
                    wrd3:=readWrd(wrd[(i+1)..(j-2)]);//the wrd in the brackets
                end if;
                if j le #wrd and wrd[j] eq "^" then
                    j+:=1;
                    if wrd[j] eq "-" then//invert
                        j+:=1;
                        wrd3:=invWrd(wrd3);
                    end if;
                    k:=j;//3rd index in wrd
                    //now find the digit
                    while k le #wrd and wrd[k] in digs do
                        k+:=1;
                    end while;
                    ind:=StringToInteger(wrd[j..(k-1)]);
                    wrd2 cat:= wrd3^ind;
                    i:=k;
                else//no operation
                    wrd2 cat:= wrd3;
                    i:=j;
                end if;
            elif wrd[i] eq "^" then
                //remove previous letter then deal with power
                j:=i+1;//second index in wrd
                if wrd[j] eq "-" or wrd[j] in digs then
                    wrd3:=wrd2[#wrd2];
                    wrd2:=wrd2[1..(#wrd2-1)];
                    if wrd[j] eq "-" then
                        j+:=1;
                        wrd3:=invWrd(wrd3);
                    end if;
                    k:=j;//3rd index in wrd
                    //now find the digit
                    while k le #wrd and wrd[k] in digs do
                        k+:=1;
                    end while;
                    ind:=StringToInteger(wrd[j..(k-1)]);
                    wrd2 cat:= wrd3^ind;
                    i:=k;
                else//error
                    print "error in readWrd. unsupported power:", wrd[j], 
                        " ignoring";
                    print "wrd=", wrd;
                    i+:=1;
                end if;
            elif wrd[i] in ALPH cat alph then//add letter
                wrd2 cat:= wrd[i];
                i+:=1;
            elif wrd[i] eq "*" or wrd[i] in ws then//skip
                i+:=1;
            else//error
                print "unknown character in readWrd", wrd[i],"character ignored";
                print "wrd=", wrd;
                i+:=1;
            end if;
        end while;
        return wrd2;
    end function;

    /*colWrd (columns of word)
        converts wrd to a sequence of numbers corresponding to the columns of CT*/
    colWrd:=function(colLets, wrd);
        seq:=[];//return value
        i:=1;//index in wrd
        while i le #wrd do
            Append(~seq, Index(colLets, wrd[i]));
            i+:=1;
        end while;
        return seq;
    end function;

    /*newDef (new definition)
        updates all tables for a new coset defined to equal to cos*gen*/
    newDef:=procedure(cos, gen,~CT, ~auxTab, ~PT, ~POL1, ~ded, colInv)
        ncol:=#CT[1];//number of columns
        //add coset to tables
        Append(~CT, [0:i in [1..ncol]]);           
        Append(~auxTab, [#CT,0,0,0]);                     
        Append(~PT, [[**]:i in [1..ncol]]);           
        Append(~POL1, [**]);      
        //update CT
        CT[#CT, colInv[gen]]:=cos;
        CT[auxTab[cos,1],gen]:=#auxTab;
        //update ded
        Append(~ded, [#auxTab, colInv[gen]]);       
        Append(~ded, [cos, gen]);         
        //update auxTab
        auxTab[#auxTab, 3]:=cos;
        auxTab[#auxTab, 4]:=gen;   
        //update PT
        Insert(~PT[cos, gen], 1, [*#auxTab, [**]*]);      
        Insert(~PT[#auxTab, colInv[gen]], 1, [*cos, [**]*]);                                        
    end procedure;

    /*invPt (invert proof table entry)
        takes a pt entry (p) and gives its inverse*/
    invPt:=function(p)
        i:=#p[2];//index in p[2]
        p2:=[*p[2][1],[**]*];//return value
        while i ge 1 do
            if Type(p[2][i]) eq RngIntElt then//add number
                Append(~p2[2], p[2][i]);
            else//add inverse proof item
                Append(~p2[2], invPItem(p[2][i]));
            end if;
            i-:=1;
        end while;
        return p2;
    end function;

    /*invPf (invert proof (chain))
        takes a proof chain (chn) and gives its inverse.
        note this is almost the same are invPt, but only the second part of
        a proof table entry is given and returned. This is needed sometimes.*/
    invPf:=function(chn)
        i:=#chn;//index in chn
        chn2:=[**];//return value
        while i ge 1 do
            if Type(chn[i]) eq RngIntElt then//add number
                Append(~chn2, chn[i]);
            else//add inverse proof item
                Append(~chn2, invPItem(chn[i]));
            end if;
            i-:=1;
        end while;
        return chn2;
    end function;

    /*ptBld (proof table entry builder)
        creates a PT entry for the deduction cos2*rel[ind]=cos1.
        rel is the relation or generator used to make the deduction
        genFlag is true is rel corresponds to a generator, false otherwise
        ind is the index in rel where the deduction was made */
    ptBld:=function(cos1, cos2, ind, rel, genFlag, CT, auxTab, colLets, colInv)
        p:=[*cos1, [*cos2*]*]; //new PT entry
        row:=cos2;//current coset
        //trace rel from ind to the end of rel
        for q in rel[(ind+1)..#rel] do 
            Append(~p[2], colLets[q]);//add generator
            row:= CT[auxTab[row][1],q];//get next coset
            Append(~p[2], row);//add next coset
        end for;
        // add the inverse gen/rel
        if (genFlag) then
            temp:="[";//rel is a generator of H
        else
            temp:="(";//rel is a relation of G
        end if;
        qj:=#rel;//index in rel
        while qj ge 1 do//add rel as letters
            temp cat:=colLets[colInv[rel[qj]]];
            qj-:=1;
        end while;
        if (genFlag) then//end rel
            temp cat:="]";
        else
            tempcat:=")";
        end if;
        Append(~p[2], temp);//add proof item to p
        // now trace rel from 1 to ind
        Append(~p[2], row);
        for q in rel[1..(ind-1)] do
            Append(~p[2], colLets[q]);//add letter of the generator
            row:= CT[auxTab[row][1],q];
            Append(~p[2], row);//add next coset
        end for;
        if (row ne cos1) then//error
            print "error in ptBld. row ne cos1";
        end if;
        return p;
    end function;

    /*redunProc (redundancy proccessor)
        processes the redundancy cos1=cos2, updating CT, auxTab and POL1 as required
        This is used for secondary coincidences. ptwrd gives information about 
        how this coincidence resulted from the primary coincidence.
        redlist holds the list of redundancies to process*/
    redunProc:=procedure(cos1, cos2, ptwrd, ~CT, ~auxTab, ~POL1, colLets, 
        colInv, ~redlist)
        //first find the chain chn1 to the coset rep r1 of cos1
        chn1:=[*cos1*];
        r1:= cos1;//current coset
        while (auxTab[r1][2] gt 0) do
            Append(~chn1, "=");
            r1:= auxTab[r1][2];
            Append(~chn1, r1);
        end while;
        //now find the chain to the coset rep of cos2, chn2
        chn2:=[*cos2*];
        r2:= cos2;//current coset
        while (auxTab[r2][2] gt 0) do
            Append(~chn2, "=");
            r2:=auxTab[r2][2];
            Append(~chn2, r2);
        end while;
        if r1 ne r2 then//coset representatives are not equal
            p:=[*r2, invPf(chn1)*];//to be added to POL1
            //start with reverse of chn1, from r1 to cos1
            p[2] cat:=ptwrd;//add pf of cos1=cos2
            p[2] cat:=chn2;//add chain for cos2=r2
            if r2 gt r1 then
                p:=invPt(p);
                auxTab[r2][2]:=r1;
                Insert(~POL1[r2],1,p);
            else
                auxTab[r1][2]:=r2;
                Insert(~POL1[r1],1,p);
            end if;
            Append(~redlist, [r1,r2]);
        end if;
    end procedure;

    /*coinc (coincidence)
        processes the coincidence cos1=cos2
        coinc works with redunProc to trace all subsequent redundancies
        ind is the index in ptrel
        ptrel holds the relation/generator used to get the coincidence.
        ptgen is positive if ptrel is a generator of H, false otherwise*/
    coinc:=procedure(cos1, cos2, ind, ptgen, ptrel, ~ded, ~auxTab, ~CT, ~PT, 
    ~POL1, colLets, colInv) 
        ncol:=#CT[1];//number of columns of CT/PT
        redlist:=[[cos1, cos2]];//redundancies to process
        //update POL1
        row:=cos2;//current coset
        p:=[*cos1, [*row*]*]; //our new POL1 entry		
        //forward scan from ind+1 to end of ptrel
        qj:=ind+1;//index in ptrel
        while qj le #ptrel do
            Append(~p[2], colLets[ptrel[qj]]);
            row:= CT[auxTab[row][1]][ptrel[qj]];
            Append(~p[2], row);
            qj+:=1;
        end while;
        // add the inverse gen/rel
        if (ptgen) then
            temp:="[";
        else
            temp:="(";
        end if;
        qj:= #ptrel;//index in ptrel
        while qj ge 1 do
            temp cat:= colLets[colInv[ptrel[qj]]];
            qj-:=1;
        end while;
        if (ptgen) then
            temp cat:= "]";
        else
            temp cat:=")";
        end if;
        Append(~p[2], temp);//add proof item to temp
        //from 1 to ind
        Append(~p[2], row);
        qj:=1;//index in ptrel
        while qj le ind do
            q:=ptrel[qj];
            Append(~p[2], colLets[q]);
            row:= CT[auxTab[row][1]][q];
            Append(~p[2], row);
            qj+:=1;
        end while;
        if cos1 gt cos2 then
            p:=invPt(p);//need reverse proof
            redcos:=cos1;//redundant coset
            auxTab[cos1][2]:=cos2;	
        else
            auxTab[cos2][2]:=cos1;
            redcos:=cos2;//redundant coset
        end if;
        if (row ne cos1) then//error
            print "error in coinc. row/cos mismatch";
            print "row=", row;
            print "redcos=", redcos;
            print "cos1=", cos1;
            print "cos2=", cos2;
            print "p=", p;
            read str;
        end if;        
        if #POL1 ge redcos and (POL1[redcos] ne [**]) then//error
            print "error in coinc. POL entry not null";
            read str;
        end if;
        POL1[redcos]:=[*p*];
        //now process redundancies
        while #redlist gt 0 do 
            c1:=redlist[1][1];
            c2:=redlist[1][2];
            Remove(~redlist,1);
            while auxTab[c1][1] eq 0 do
                c1:=auxTab[c1][2];
            end while;
            while auxTab[c2][1] eq 0 do
                c2:=auxTab[c2][2];
            end while;
            if c2 gt c1 then
                src:=c2;//source row
                dst:=c1;//destination row
            elif c1 gt c2 then
                src:=c1;//source row
                dst:=c2;//destionation row
            else//must be equal. no need to process.
                src:=c1;//prevent processing
                dst:=c1;//prevent processing
            end if;
            //If the two reps are equal there's nothing to do.
            //If not, data has to be moved from src (source) to dst (destination)
            if (src ne dst) then
                row:=CT[auxTab[src][1]];//information to be moved
                Remove(~CT,auxTab[src][1]);//remove redundant row from CT
                //update auxTab[1]
                for j in [1..#auxTab] do
                    if auxTab[j][1] gt auxTab[src][1] then
                        auxTab[j][1]-:=1;
                    end if;
                end for;    
                auxTab[src][1]:=0;
                auxTab[src][2]:=dst; 
                //we move all information from row to the dst row
                for i in [1..ncol] do 
                    dsti:= CT[auxTab[dst][1],i];//info in dst row, column i
                    j:= colInv[i];
                    if (row[i] ne 0) then//info to move
                        if (row[i] eq dst) then
                            if (dsti eq 0) or (dsti eq src) then//no new coincidences
                                //update CT
                                CT[auxTab[dst][1],i]:= dst;
                                CT[auxTab[dst][1],j]:= dst;
                                //avoid reprocessing
                                if row[j] eq dst then
                                    row[j]:=0;
                                end if;
                                //add to ded
                                Append(~ded, [dst,i]);
                                Append(~ded, [dst,j]);
                                //update PT
                                p:=[*dst, [*dst, "=", src, colLets[i], dst*]*];
                                Insert(~PT[dst,i],1,p);
                                p:=[*dst, [*dst, colLets[j], src, "=", dst*]*];
                                Insert(~PT[dst,j],1,p);
                            elif (dsti eq dst) then//error
                                print "error in coinc: col contains duplicate entry";
                                print "dst=", dst;
                                print "src=", src;
                                print "row=", row;
                                print "i=", i;
                                print "auxTab=";
                                print auxTab;
                                print "CT=";
                                print CT;
                            else //new coincidence row[i]=dst=dsti
                                ptwrd:=[*colLets[j], dst, "=", src, colLets[i]*];
                                redunProc(dsti,dst, ptwrd, ~CT, 
                                    ~auxTab, ~POL1, colLets, colInv, ~redlist);
                                //set inverse to 0 to avoid reprocessing
                                CT[auxTab[dst][1],j]:=0;
                            end if;
                        elif (row[i] eq src) then
                            //note: this means row[j]=src too. 
                            //we do both columns now
                            if (dsti eq 0) then	
                                dstj:= CT[auxTab[dst][1],j];
                                if (dstj eq 0) then
                                    //update CT
                                    CT[auxTab[dst][1],i]:= dst;
                                    CT[auxTab[dst][1],j]:= dst;
                                    //add to ded
                                    Append(~ded, [dst,i]);
                                    Append(~ded, [dst,j]);
                                    //update PT
                                    p:=[*dst, [*dst, "=", src, colLets[i], 
                                        src, "=", dst*]*];
                                    Insert(~PT[dst,i],1,p);
                                    p:=[*dst, [*dst, "=", src, colLets[j], 
                                        src, "=", dst*]*];
                                    Insert(~PT[dst,j],1,p);
                                else//coincidence dstj=dst
                                    ptwrd:=[*colLets[i], dst, "=", src, colLets[j], src, "="*];
                                    redunProc(dstj, dst, ptwrd, ~CT, ~auxTab, ~POL1, colLets,
                                        colInv, ~redlist);
                                end if;
                            elif (dsti eq dst) then	
                                //do nothing, CT[dst,i] and CT[dst,j] already correct
                            elif (dsti eq src) then//error
                                print "error in coinc. row[i]=src=dsti";
                            else //coincidence dsti=src=dst
                                ptwrd:=[*"=", src, colLets[j], src, "=", dst, colLets[i]*];
                                redunProc(dst,dsti, ptwrd, ~CT, ~auxTab, ~POL1, colLets, 
                                    colInv, ~redlist);
                                dstj:= CT[auxTab[dst][1],j];
                                if (dstj ne 0 and dstj ne dsti) then
                                //another coincidence
                                    ptwrd:=[*"=", src, colLets[i], src, "=", dst, colLets[j]*];
                                    redunProc(dst,dstj, ptwrd, ~CT, ~auxTab, ~POL1, colLets, 
                                        colInv, ~redlist);
                                end if;
                            end if;
                            row[j]:=0;//avoid reprocessing
                        else
                            if (dsti eq 0) then //just update
                                //update CT
                                CT[auxTab[dst][1],i]:= row[i];
                                CT[auxTab[row[i]][1],j]:= dst;
                                //add to ded
                                Append(~ded, [dst,i]);
                                Append(~ded, [row[i],j]);
                                //update PT
                                p:=[*row[i], [*dst, "=", src, colLets[i], row[i]*]*];
                                Insert(~PT[dst,i],1,p);
                                p:=[*dst, [*row[i], colLets[j], src, "=", dst*]*];
                                Insert(~PT[row[i],j],1,p);
                            elif (dsti eq dst) then	//coincidence dsti=row[i]=dst
                                ptwrd:=[*colLets[j], src, "=", dst, colLets[i]*];
                                CT[auxTab[row[i]][1],j]:=0;
                                redunProc(row[i], dst, ptwrd, ~CT, ~auxTab, ~POL1, colLets, 
                                    colInv, ~redlist);
                            elif (dsti eq src) then	//coincidence dsti=row[i]=src=dst
                                ptwrd:=[*colLets[j], src, "=", dst, colLets[i], src, "="*];
                                CT[auxTab[row[i]][1],j]:=0;
                                redunProc(row[i], dst, ptwrd, ~CT, ~auxTab, ~POL1, colLets, 
                                    colInv, ~redlist);
                            elif (dsti eq row[i]) then//error
                                print "error in coinc: dsti eq row[i]";
                            else //coincidence dsti=row[i]
                                ptwrd:=[*colLets[j], src, "=", dst, colLets[i]*];
                                CT[auxTab[row[i]][1],j]:=0;
                                redunProc(row[i], dsti, ptwrd, ~CT, ~auxTab, ~POL1, colLets, 
                                    colInv, ~redlist);
                            end if;
                        end if;
                    end if;
                end for;
            end if;
        end while;
    end procedure;

    /*apply (apply relator)
        applies the word in rel to the coset cos. then cosets are defined to 
        complete the word. ptgen is a flag which is true if rel is actually a 
        generator.
        fillflag=-1 if unlimited cosets can be added or 
        gives max number of cosets to add*/
    apply:=procedure(cos, rel, ~CT, ptgen, ~ded, ~auxTab, ~POL1, ~PT, colLets,
    colInv, fillFlag)
        app_flag:=true;//changes to false if #CT gt maxrow
        fwdcos:=cos;//tacks cosets in forward scan
        bwdcos:=cos;//tracks cosets in backwards scan
        //scan rel forwards from cos, until we find an undefined CT entry
        fwd:=1;//position of rel in forward scan
        while fwd le #rel do
            if CT[auxTab[fwdcos][1], rel[fwd]] ne 0 then//coset is defined
                fwdcos:=CT[auxTab[fwdcos][1], rel[fwd]];
                fwd+:=1;
            else //undefined entry in CT found
                break;
            end if;
        end while;
        bwd:=#rel;//position of rel in backward scan
        while bwd ge fwd do 
            j:=rel[bwd];
            ji:= colInv[j];//need inverse because we are scanning backwards
            if CT[auxTab[bwdcos][1], ji] ne 0 then//coset defined
                bwdcos:=CT[auxTab[bwdcos][1], ji];
            else //undefined CT entry found
                if (bwd eq fwd) then//only one gap
                    if CT[auxTab[fwdcos][1],j] ne 0 then
                        //CT has been filled since fwd scan. possible coincidence
                        fwdcos:= CT[auxTab[fwdcos][1], j];	
                    else //fill gap
                        //update CT
                        CT[auxTab[bwdcos][1], ji]:= fwdcos; 
                        CT[auxTab[fwdcos][1],j]:= bwdcos;
                        //add to ded
                        Append(~ded, [bwdcos, ji]);
                        Append(~ded, [fwdcos,j]);
                        //update PT
                        p:=ptBld(fwdcos, bwdcos, fwd, rel, ptgen, CT, auxTab, colLets, colInv);
                        Insert(~PT[bwdcos][ji], 1,p);
                        Insert(~PT[fwdcos][j],1,invPt(p));
                        fwdcos:= bwdcos;//Prevent false coincidence
                    end if;
                elif fillFlag ge bwd-fwd then // Define a new coset
                    if (#CT gt maxrow) then	//Overflow
                        print "#CT gt maxrow";
                        app_flag:=false;
                        break;
                    end if;
                    newDef(bwdcos, ji, ~CT, ~auxTab, ~PT, ~POL1, ~ded, colInv); 
                    bwdcos:=#auxTab;
                    while fwd le #rel do//update fwd
                        if CT[auxTab[fwdcos][1], rel[fwd]] ne 0 then
                        //coset is defined
                            fwdcos:=CT[auxTab[fwdcos][1], rel[fwd]];
                            fwd+:=1;
                        else //undefined entry in CT found
                            break;
                        end if;
                    end while;
                else//nothing to do
                    fwdcos:=bwdcos;//Prevent false coincidence
                    break;
                end if;
            end if;
            bwd-:=1;
        end while;
        if fwdcos ne bwdcos and bwd lt fwd and app_flag then//coincidence!
            coinc(fwdcos, bwdcos, bwd, ptgen, rel, ~ded, ~auxTab, ~CT, ~PT, ~POL1, 
                colLets, colInv);
        end if;
    end procedure;

    /* checkDed (check deductions)
        ded is a stack of CT coordinates which are to be tested with 
        this procedure
        checkDed processes all outstanding deductions on the stack by scanning all
        relevant relators from this position*/
    checkDed:=procedure(~ded, ~auxTab, ~CT, ccRels, ~POL1, ~PT, colLets, colInv)
        while (#ded ge 1) do
            row:= ded[#ded][1];
            col:= ded[#ded][2];
            Prune(~ded);
            if row le 0 or col le 0 or row gt #auxTab or col gt #ccRels then//error
                print "error in checkDed: invalid col or row";
                print ded, ", ", row, ", ",col;
                ded:=[];
            elif (auxTab[row][2] eq 0) then //not redundant
                i:=1;//index for ccRels[col]
                while i le #ccRels[col] and auxTab[row][2] eq 0 do
                    //note: row doesn't change in loop but auxTab might!
                    //auxTab[row][2] ne 0 mean coset has become redundant
                    apply(row, ccRels[col][i], ~CT, false, ~ded, ~auxTab, ~POL1, ~PT, 
                        colLets, colInv, 0);
                    i+:=1;
                end while;
            end if;
        end while;
    end procedure;

/*end of utility functions*/

/*proof word utility functions*/
    /*revPWrd (reverse proof word)
        reverses a proof word, that is gives the inverse, 
        preserving proof specific formatting*/
    revPWrd:=function(wrd)
        wrd2:=[];//return value
        i:=#wrd;//index in wrd
        while i ge 1 do
            Append(~wrd2,invPItem(wrd[i]));//add inverse
            i-:=1;
        end while;
        return wrd2;
    end function;
        
    /*strCat (string catonate)
        catonates str1 and str2, removing inverses from the pt of catonation*/
    strCat:=function(str1, str2)
        k:=1;//index in str2
        while k le #str2 do
            if #str1 eq 0 then//str1= start of str2
                str1:=str2[k..#str2];
                k:=#str2+1;//end loop
            elif isInvGen(str1[#str1], str2[k]) then//cancel
                str1:=str1[1..#str1-1];
                k+:=1;
            else//add end of str2 to str
                str1:=str1 cat str2[k..#str2];
                k:=#str2+1;//end loop
            end if;
        end while; 
        return str1;
    end function;

    /*simp1 (simplify 1)
        removes all brackets, and removes adjacent xX pairs. 
        This gives wrd1 as a word in the generators of G*/
    simp1:=function(wrd1)
        wrd:="";//return value
        for i in [1..#wrd1] do
            for j in [1..#wrd1[i]] do
                if wrd1[i][j] in alph or wrd1[i][j] in ALPH then
                    if #wrd eq 0 then
                        wrd:=wrd1[i][j];
                    elif isInvGen(wrd1[i][j],wrd[#wrd]) then
                        wrd:=wrd[1..(#wrd-1)];//remove last item
                    else
                        wrd cat:=wrd1[i][j];
                    end if;
                //else wrd1[i,j] is a bracket
                end if;
            end for;
        end for;
        return wrd;
    end function;

    /*simp2 (simplify 2)
        removes anything inside () brackets then removes adjacent xX pairs 
        between ][. 
        This function is used to give wrd1 as a word in the generators of H*/
    simp2:=function(wrd1)
        wrd:="";//return value
        for i in [1..#wrd1] do
            if wrd1[i][1] eq "[" then
                wrd cat:=wrd1[i];
            elif #wrd1[i] eq 1 then
                if #wrd eq 0 then
                    wrd:=wrd1[i];
                elif isInvGen(wrd1[i],wrd[#wrd]) then
                    Prune(~wrd);//remove last item
                else
                    wrd cat:=wrd1[i];
                end if;
            //else () so ignore
            end if;
        end for;
        return wrd;
    end function;

    /*simp1Cat (simplify 1 concatonation)
        add a proof item to a simp1 word wrd*/
    simp1Cat:=procedure(~wrd, item);
        if #item gt 1 then//remove brackets
            item:=item[2..(#item-1)];
        end if;
        i:=1;//index in item
        while i le #item do
            if #wrd eq 0 then//add the rest of item
                wrd:=item[i..#item];
                i:=#item+1;//end loop
            elif isInvGen(wrd[#wrd], item[i]) then//cancel
                Prune(~wrd);//remove last item
                i+:=1;
            else//add end of str2 to str
                wrd cat:=item[i..#item];
                i:=#item+1;//end loop
            end if;
        end while; 
    end procedure;

    /*simp2Cat (simplify 2 concatonation)
        add a proof item to a simp2 word wrd*/
    simp2Cat:=procedure(~wrd, item);
        if item[1] ne "(" then
            if #wrd eq 0 then
                wrd:=item;
            elif #item eq 1 and isInvGen(wrd[#wrd], item) then
                Prune(~wrd);
            else
                wrd cat:= item;
            end if;
        //else do nothing
        end if;
    end procedure;

    /*simpRedCat (simple reduced catonate)
        gives the reduced catonate of wrd1 and wrd2. That is, it removes 
        any Aa, () or [] pairs which appear at the point of catonation.
        It is assumed that wrd1 and wrd2 are already reduced.*/
    simpRedCat:=function(wrd1, wrd2)
        i:=1;//index in wrd2
        while i le #wrd1 and i le #wrd2 do
            if isInvPItem(wrd1[#wrd1+1-i], wrd2[i]) then
                i+:=1;
            else
                return wrd1[1..(#wrd1+1-i)] cat wrd2[i..#wrd2];
            end if;
        end while;
        if i gt #wrd1 then
            if i gt #wrd2 then
                return [];
            else
                return wrd2[i..#wrd2];
            end if;
        elif i gt #wrd2 then
            return wrd1[1..(#wrd1-i+1)];
        else//error
            print "error in simpRedCat";
            return [];
        end if;
    end function;

    forward redCat;
    /*splitRedCat (split reduced catonate)
        wrd1[i] and wrd2[j] should be inverse relators of G or generators of H. 
        This function splits these items*/
    splitRedCat:=function(wrd1, i, wrd2, j)
        item1:=[];
        ind:=2;//index in wrd1[i]
        while ind lt #wrd1[i] do
            Append(~item1, wrd1[i][ind]);
            ind+:=1;
        end while;
        item2:=[];
        ind:=2;//index in wrd2[j]
        while ind lt #wrd2[j] do
            Append(~item2, wrd2[j][ind]);
            ind+:=1;
        end while;
        //find wrd3
        if i gt 1 then//add start of wrd1
            wrd3:=redCat(wrd1[1..(i-1)],item1);
        else
            wrd3:=item1;
        end if;
        //find wrd4. 
        if i lt #wrd1 then
            if j gt 1 then
                wrd4:=redCat(wrd1[(i+1)..#wrd1],wrd2[1..(j-1)]);
            else
                wrd4:=wrd1[(i+1)..#wrd1];
            end if;
        else
            if j gt 1 then
                wrd4:=wrd2[1..(j-1)];
            else
                wrd4:=[];
            end if;
        end if;
        //find wrd5
        if j lt #wrd2 then
            wrd5:=redCat(item2, wrd2[(j+1)..#wrd2]);
        else
            wrd5:=item2;
        end if;
        return redCat(redCat(wrd3, wrd4), wrd5);
    end function;

    /*relRedCat (relator reduced catonate)
        finds the last relator (of G) in wrd1 and then relators in wrd2, before the
        first generator (of H). If these are inverses and then word of generators
        (of G) inbetween them reduces to the empty word, then the relators items 
        "(xyz)" and "(ZYX)" are replaced by "x", "y", "z" and "Z", "Y", "X" 
        respectively. This is allowed since in simp1 they will be used as such, and 
        in simp2 as (xyz) and (ZYX) then will be removed and as "x", "y", "z" and 
        "Z", "Y", "X", they will end up adjacent, and thus removed.*/
    relRedCat:=function(wrd1,wrd2)
        i:=#wrd1;//index in wrd1
        jflag:=true;//stays true if no rels in wrd2
        while i ge 1 and wrd1[i][1] ne "[" do
            while i ge 1 and wrd1[i][1] ne "[" and wrd1[i][1] ne "(" do
                i-:=1;
            end while;
            if i ge 1 and wrd1[i][1] eq "(" then//rel found
                wrd3:="";//word formed by catonation of type1 items after wrd1[i]
                for ind in [(i+1)..#wrd1] do
                    if #wrd1[ind] eq 1 then//type 1
                        wrd3:=strCat(wrd3,wrd1[ind]);
                    end if;
                end for;
                j:=1;//index in wrd2
                while j le #wrd2 and wrd2[j][1] ne "[" do
                    if #wrd2[j] eq 1 then//gen of G
                        wrd3:=strCat(wrd3,wrd2[j]);
                        j+:=1;
                    else
                        jflag:=false;//rel found
                        if #wrd3 eq 0 then//cancel if inverse
                            if isInvPItem(wrd1[i], wrd2[j]) then
                                return splitRedCat(wrd1, i, wrd2, j);
                            else//can't cancel
                                j+:=1;
                            end if;
                        else//can't cancel
                            j+:=1;
                        end if;
                    end if;
                end while;
                if jflag then//no rels at start of wrd2
                    return wrd1 cat wrd2;
                else//try next rel in wrd1
                    i-:=1;
                end if;
            else//no more rels in end of wrd1
                return wrd1 cat wrd2;
            end if;
        end while;
        return wrd1 cat wrd2;
    end function;
    
    /*genRedCat (generator reduced catonate)
        finds the last generator (of H) in wrd1 and the first generator in wrd2,
        if these are inverses then the generators items "[xyz]" and "[ZYX]" are 
        replaced by "x", "y", "z" and "Z", "Y", "X" respectively. 
        This is allowed since in simp1 they will be used as such, and in simp2 
        [xyz] and [ZYX] will be adjacent, and thus removed.*/
    genRedCat:=function(wrd1, wrd2)
        i:=#wrd1;//index in wrd1
        while i ge 1 do//find last gen in wrd1
            if wrd1[i][1] eq "[" then//gen found
                break;
            else
                i-:=1;
            end if;
        end while;
        if i lt 1 then//no gens in wrd1
            return relRedCat(wrd1,wrd2);
        end if;
        j:=1;//index in wrd2
        while j le #wrd2 do//find first gen in wrd2
            if wrd2[j][1] eq "[" then//gen found
                break;
            else
                j+:=1;
            end if;
        end while;
        if j gt #wrd2 then//no gens in wrd2
            return relRedCat(wrd1,wrd2);
        end if;
        //if we get to here we have 2 gens to compare.
        if isInvPItem(wrd1[i], wrd2[j]) then//split and cat
            return splitRedCat(wrd1, i, wrd2, j);
        else
            return relRedCat(wrd1,wrd2);
        end if;
    end function;

    /*relRedCat2 (relator reduced catonate type 2)
        for each type 2 item r1 at index i1 in wrd1 and each type2 item r2
        at index i2 in wrd2, if simp1 of (wrd1[i1+1..#wrd1] cat wrd2[1..i2-1])=""
        then remove r1 and r2.*/
    relRedCat2:=function(wrd1,wrd2)
        i:=1;//index in wrd2
        str1:="";//word formed by catonation of all items before wrd2[i]
        while i le #wrd2 do
            if wrd2[i][1] ne "(" then// add to str1
                if #wrd2[i] gt 1 then
                    str2:=wrd2[i][2..#wrd2[i]-1];
                else
                    str2:=wrd2[i][1];
                end if;
                str1:=strCat(str1, str2);
                i+:=1;   
            else//rel found
                relflag:=true;//false if a rel is found in wrd1
                j:=#wrd1;//index in wrd1
                str2:=str1;//add catonation with wrd1 to str2
                while j ge 1 do
                    if wrd1[j][1] eq "(" and #str2 eq 0 and 
                    isInvPItem(wrd2[i], wrd1[j]) then//cancel rels
                        wrd1:=redCat(wrd1[1..j-1], wrd1[j+1..#wrd1]);//remove wrd1[j]
                        wrd2:=redCat(wrd2[1..i-1], wrd2[i+1..#wrd2]);//remove wrd2[i]
                        return redCat(wrd1,wrd2);
                    else//add to str2
                        if wrd1[j][1] eq "(" then//rel found
                            relflag:=false;
                        end if;
                        if #wrd1[j] gt 1 then//remove brackets
                            str3:=wrd1[j][2..#wrd1[j]-1];
                        else
                            str3:=wrd1[j][1];
                        end if;
                        str2:=strCat(str3, str2);
                        j-:=1;
                    end if;
                end while;
                if relflag then
                    return genRedCat(wrd1,wrd2);
                end if;
                //add wrd2[i] to str1 and move to next i
                str1:=strCat(str1, wrd2[i][2..#wrd2[i]-1]);
                i+:=1;
            end if;
        end while;
        return genRedCat(wrd1,wrd2);
    end function;

    /*redCat2 (reduced catonate type 2)
        removes pairs of inverse type1 items i1 and i2 when they surround a type2 r item
        and simp1(i1, r, i2)=r*/
    redCat2:=function(wrd1, wrd2)
        if #wrd1[#wrd1] eq 1 then//ends with gen
            if wrd2[1][1] eq "(" and #wrd2 gt 1 then//rel start
                if #wrd2[2] eq 1 and isInvGen(wrd1[#wrd1], wrd2[2]) then
                    if wrd2[2] eq wrd2[1][2] then//remove
                        str:="(";
                        str cat:=wrd2[1][3..#wrd2[1]-1];
                        str cat:=wrd2[1][2];
                        str cat:=")";
                        Remove(~wrd1,#wrd1);
                        wrd2:=redCat([str], wrd2[3..#wrd2]);
                        return redCat(wrd1, wrd2);
                    elif wrd1[#wrd1] eq wrd2[1][#wrd2[1]-1] then//remove
                        str:="(";
                        str cat:=wrd2[1][#wrd2[1]-1];
                        str cat:=wrd2[1][2..#wrd2[1]-2];
                        str cat:=")";
                        Remove(~wrd1, #wrd1);
                        wrd2:=redCat([str], wrd2[3..#wrd2]);
                        return redCat(wrd1, wrd2);
                    end if;
                end if;
            end if;
        elif wrd1[#wrd1][1] eq "(" and #wrd1 gt 1 then//ends with rel
            if #wrd2[1] eq 1 then//gen start
                if #wrd1[#wrd1-1] eq 1 and isInvGen(wrd1[#wrd1-1], wrd2[1]) then
                    if wrd2[1] eq wrd1[#wrd1][2] then//remove
                        str:="(";
                        str cat:=wrd1[#wrd1][3..#wrd1[#wrd1]-1];
                        str cat:=wrd1[#wrd1][2];
                        str cat:=")";
                        Remove(~wrd2, 1);
                        wrd1:=redCat(wrd1[1..#wrd1-2], [str]);
                        return redCat(wrd1, wrd2);
                    elif wrd1[#wrd1-1] eq wrd1[#wrd1][#wrd1[#wrd1]-1] then//remove
                        str:="(";
                        str cat:=wrd1[#wrd1][#wrd1[#wrd1]-1];
                        str cat:=wrd1[#wrd1][2..#wrd1[#wrd1]-2];
                        str cat:=")";
                        Remove(~wrd2,1);
                        wrd1:=redCat(wrd1[1..#wrd1-2], [str]);
                        return redCat(wrd1, wrd2);
                    end if;
                end if;
            end if;
        end if;
        return relRedCat2(wrd1, wrd2);
    end function;

    /*redCat (reduced catonate)
        gives the reduced catonate of wrd1 and wrd2. It is assumed that wrd1 
        and wrd2 are already reduced. Uses genRedCat to remove inverse 
        generators and relRedCat to remove inverse relations*/
    redCat:=function(wrd1, wrd2)
        i:=1;//index in wrd2
        while i le #wrd1 and i le #wrd2 do
            if isInvPItem(wrd1[#wrd1+1-i], wrd2[i]) then
                i+:=1;
            else
                return redCat2(wrd1[1..(#wrd1+1-i)],wrd2[i..#wrd2]);
            end if;
        end while;
        if i gt #wrd1 then//all of wrd1 cancelled
            if i gt #wrd2 then//wrd1 and wrd2 are inverse
                return [];
            else
                return wrd2[i..#wrd2];
            end if;
        elif i gt #wrd2 then//wrd2 cancelled
            return wrd1[1..(#wrd1-i+1)];
        else//error
            print "error in redCat";
            return [];
        end if;
    end function;

    /*simpWrd (simplify word)
        this is an additional method of simplification with may reduce the 
        length of a particularly long proof word. 
        This algorithm searches for sections w of wrd which have the property 
        that s1(w) in rels and s2(w)=1G. Such sections can be replaced by
        a single type two proof item equal to s1(w).*/
    simpWrd:=procedure(~wrd, rels)
        //add to rels
        rels2:=rels;
        //add all rotations and inverses of rels
        for i in [1..#rels2] do
            r:=rels2[i];
            //add rotations
            while true do
                r:=r[2..#r] cat r[1];
                if r in rels then
                    break;//all rotations added
                else
                    Append(~rels, r);
                end if;
            end while;
            //create inverse
            j:=#r;
            r2:="";//holds inverse
            while j ge 1 do
                r2 cat:=caseConv(r[j]);
                j-:=1;
            end while;
            if r2 notin rels then
                Append(~rels, r2);
                //add rotations
                while true do
                    r2:=r2[2..#r2] cat r2[1];
                    if r2 in rels then
                        break;//all rotations added
                    else
                        Append(~rels, r2);
                    end if;
                end while;
            end if;
        end for;
        i:=1;//index in wrd
        while i lt #wrd do
            s1:=simp1([wrd[i]]);//s1 of wrd[i..j]
            s2:=simp2([wrd[i]]);//s2 of wrd[i..j]
            j:=i+1;//second index in wrd
            while j le #wrd do
                simp1Cat(~s1, wrd[j]);
                simp2Cat(~s2, wrd[j]);
                if s1 in rels and j-i ge 3 and #s2 eq 0 then
                    //count type 2,3 items
                    cnt:=0;
                    for k in [i..j] do
                        if #wrd[k] gt 1 then
                            cnt+:=1;
                        end if;
                    end for;
                    if cnt gt 1 then
                        wrd2:=redCat(wrd[1..(i-1)], ["(" cat s1 cat ")"]);
                        wrd:=redCat(wrd2, wrd[(j+1)..#wrd]);
                        if i gt 100 then
                            i-:=100;
                        else
                            i:=0;
                        end if;
                        break;
                    end if;
                end if;
                j+:=1;
            end while;
            i+:=1;
        end while;
    end procedure;

    /*HrelSimp (H relation simplifier)
        Allows a user to enter a know relation of H involving a single generator
        of H (that is the relator is a power g^n). 
        Simplify by adding G^n, (g^n) and removing the square brackets of the 
        generators to simplify*/
    HrelSimp:=procedure(~wrd, g, n)
        print "#wrd=", #wrd;
        sg:=[];//split of g
        gi:=invWrd(g);//inverse of g
        sgi:=[]; //split of gi
        x:=[];//proof word to add if g^n found
        r:="(";//rel
        for i in [1..#g] do
            Append(~sg, g[i]);
            Append(~sgi, gi[i]);
        end for;
        for i in [1..n] do
            x cat:= sgi;
            r cat:= g;
        end for;
        r cat:=")";
        Append(~x, r);
        i:=1;//first index of wrd
        while i lt #wrd do
            if wrd[i][1] eq "[" and wrd[i][2..#wrd[i]-1] eq g then
                j:=i+1;
                inds:=[i];
                cnt:=1;
                while j le #wrd and cnt lt n do
                    if wrd[j][1] eq "[" then
                        if wrd[i] eq wrd[j] then
                            Append(~inds, j);
                            cnt+:=1;
                        else
                            break;
                        end if;
                    end if;
                    j+:=1;
                end while;
                if cnt eq n then//rel found
                    wrd1:=wrd[1..i-1];
                    for j in [1..cnt-1] do
                        wrd1:=redCat(wrd1, sg);
                        wrd1:=redCat(wrd1, wrd[inds[j]+1..inds[j+1]-1]);
                    end for;
                    wrd1:=redCat(wrd1, sg);
                    wrd:=redCat(wrd1, redCat(x, wrd[inds[n]+1..#wrd]));
                    i:=0;
                end if;
            end if;
            i+:=1;
        end while;
        print "#wrd=", #wrd;
    end procedure;

    /*pfEntry (proof entry)
        creates the proof word for cos1*gen=cos2 and add to PT2 (or POL2).
        any proof words needed in the process will be added to PT2, or POL2
        if not already there*/
    forward pfEntry;
    pfEntry:=procedure(gen, cos1, cos2, ~L, colInv)
        colLets:=L[1];
        auxTab:=L[3];
        PT:=L[4];
        POL1:=L[5];
        /*first find appropriate list*/
        if gen eq 0 then //cos1=cos2
            if auxTab[cos2][2] eq cos1 then//need to swap cos1 and cos2
                pf1:=POL1[cos2];
                temp:=cos1;
                cos1:=cos2;
                cos2:=temp;
            elif auxTab[cos1][2] eq cos2 then
                pf1:=POL1[cos1];
            else//error
                print "matching error in pfEntry";
                print cos1, cos2, auxTab[cos1], auxTab[cos2];
            end if;
        else//cos1*gen=cos2
            pf1:=PT[cos1, gen];
        end if;
        pfflag:=true;
        i:=#pf1;
        while i ge 1 and pfflag do
            //find the proof word which we need for cos1 to cos2
            if pf1[i][1] eq cos2 then//found it!
                pf:=pf1[i][2];
                pfflag:=false;
            end if;
            i-:=1;
        end while;
        if pfflag then//error
            print "error in pfEntry.no valid proof word for", cos1, gen, cos2;
            print "pf1=", pf1;
            print "POL1[", cos1, "]=", POL1[cos1];
            print "POL1[", cos2, "]=", POL1[cos2];
            print "PT[", cos1, "]=", PT[cos1];
            print "PT[", cos2, "]=", PT[cos2];
        end if;
        if #pf eq 0 then//definition
            Append(~L[6][cos1,gen],[*cos2, [colLets[gen]]*]);
            Append(~L[6][cos2, colInv[gen]],[*cos1, [colLets[colInv[gen]]]*]);
            //note gen must not eq 0, since it is only 0 in redundancies
        else
            j:=1;
            pfwrd:=[];
            while j le (#pf-2) do//prove each step
                //pf[j]=current coset,pf[j+1]=pf item, pf[j+2]= next coset
                if pf[j+1] eq "=" then
                    if auxTab[pf[j]][2] eq pf[j+2] then
                        if #L[7][pf[j]] eq 0 then//fill in
                            pfEntry(0, pf[j], pf[j+2],~L, colInv);
                        end if;
                        pfwrd:=redCat(pfwrd,L[7][pf[j]][2]);
                    elif auxTab[pf[j+2]][2] eq pf[j] then
                        if #L[7][pf[j+2]] eq 0 then
                            pfEntry(0, pf[j+2], pf[j],~L, colInv);
                        end if;
                        pfwrd:=redCat(pfwrd,revPWrd(L[7][pf[j+2]][2]));
                    else//error
                        print "error in pfEntry";
                    end if;
                elif #pf[j+1] eq 1 then//type 1 pf item
                    gen2:=Index(colLets, pf[j+1]);
                    tempPfwrd:=[];
                    i:=1;
                    while i le #L[6][pf[j], gen2] do
                        if L[6][pf[j], gen2][i][1] eq pf[j+2] then
                            tempPfwrd:=L[6][pf[j], gen2][i][2];
                            break;
                        else
                            i+:=1;
                        end if;
                    end while;
                    if #tempPfwrd eq 0 then//find proof and fill in table
                        pfEntry(gen2, pf[j], pf[j+2],~L, colInv);
                        tempPfwrd:=L[6][pf[j], gen2][#L[6][pf[j], gen2]][2];
                    end if;
                    pfwrd:=redCat(pfwrd,tempPfwrd);
                else //subgroup generator or group relation
                    pfwrd:=redCat(pfwrd, [pf[j+1]]);
                end if;
                j+:=2;
            end while;
            if gen eq 0 then//updat POL2
                L[7][cos1]:=[*cos2, pfwrd*];
            else//update PT2
                Append(~L[6][cos1, gen],[*cos2,pfwrd*]);
                Append(~L[6][cos2, colInv[gen]], [*cos1,revPWrd(pfwrd)*]);
            end if;
        end if;
    end procedure;
/*End proof word utilities*/

/*user functions*/
    PEACEv2:=function(G, Hgens)
        start:=Realtime();
        /*initialise basic variables*/
            knh:=1; //knh is the first coset where the corresponding row of CT may contain 0.
            ded:=[]; /*contains a stack of positions in CT which we need to look at 
                        (ie check if relations can be used to fill holes in CT)*/
            lcount:=0; //counts the number of loops
            PT2:=[]; //stores proofwords as they are created;
            POL2:=[]; //stores proofwords (for redudancies) as they are created;
        /*basic variables initialised*/

        /*initialise group generators*/
            /*check for repeated letter, or given in upper case*/
            Ggen:=Generators(G);
            GenLets:=[];
            InvLets:=[];
            /*contains the letters corresponding to the generators of G, 
                taking only the lowercase version for each*/
            for g in Ggen do
                gstr:=Sprint(g);
                Append(~GenLets, gstr);
                Append(~InvLets, caseConv(gstr));
            end for;
            Ngens:=#GenLets;
        /*group generators initialized*/

        /*build tables*/
            ncol:=2*#GenLets;//number of colums in CT
            colLets:=GenLets cat InvLets; //labels of the column of CT
            colInv:=[(#GenLets+1)..ncol] cat [1..#GenLets];//gives inverse column
            CT:=[[0:i in [1..ncol]]];
            auxTab:=[[1, 0, 0, 0]];
                /*auxTab gives various information about each coset
                    auxTab[cos][1] gives the row of CT which corresponds to 
                        the coset cos, or 0 if it has been removed (cos is redundant)
                    auxTab[cos][2] the equivalent coset if cos is redundant, 
                        0 otherwise
                    auxTab[cos][3] gives the coset from which cos was defined
                    auxTab[cos][4] give the column (thus the generator) used in the 
                    definition of cos
                */
            PT:=[[[**]:i in [1..ncol]]];
            POL1:=[[**]];
                /*PT and POL1 are used to create proofs. 
                POL1 keeps information about redundancies,
                PT keeps information about how entries of CT were obtained*/
        /*tables built*/
            
        /*initialise group relators.*/
            /*In this section we convert Grel to relators. 
            relators is a list of the relators of G, with each relator given
            as a list of the colums which correspond.
            EG: if Grel=[aB] and Ggen=[a,b] then relators=[[1,4]]
                if Grel=[aB, Bc] and Ggen=[a,b,c] then relators=[[1,5],[5,3]]
            */
            relflag:=true;
            Grels:=Relations(G);   

            relators:=[];
            for rel in Grels do
                wrd:=Sprint(rel);
                i:=1;
                while i le #wrd and wrd[i] ne "=" do
                    i+:=1;
                end while;
                if i gt #wrd then
                    //do nothing
                elif #wrd ge i+4 and wrd[(i+1)..(i+4)] eq " Id(" then
                    wrd:=wrd[1..(i-1)];
                else
                    wrd:=wrd[1..(i-1)] cat "(" cat 
                    wrd[(i+1)..#wrd] cat ")^-1";
                end if;
                wrd2:=readWrd(wrd);
                Append(~relators, colWrd(colLets, wrd2));
            end for;
        /*group relators initialised*/

        /*initialised subggen*/
            /*In this section we convert Hgens to subggens. 
            subggens is a list of the generators of H, with each generator given
            as a list of the colums which correspond.
            EG: if HGen=[aB] and Ggen=[a,b] then subggens=[[1,4]]
                if HGen=[aB, Bc] and Ggen=[a,b,c] then subggens=[[1,5],[5,3]]
            */
            subggens:=[];
            for hgen in Hgens do
                wrd:=Eltseq(hgen);
                wrd2:=[];
                for n in wrd do
                    if n gt 0 then
                        Append(~wrd2,n);
                    else
                        Append(~wrd2,Ngens-n);
                    end if;
                end for;
                Append(~subggens, wrd2);
            end for;
        /*subggen initialised*/

        /*creation of ccRels (column cycled relations).*/
        /*ccRels gives a list of list of relations(cycled appropriately) which 
            start with the generator corresponding to the list number. These are 
            used in checkDed*/
            ccRels:=[[]:i in [1..ncol]];
            for col in [1..ncol] do
                for rel in relators do
                    for i in [1..#rel] do
                        if rel[i] eq col then
                            rel2:=rel[i..#rel] cat rel[1..(i-1)];
                            if rel2 in ccRels[col] then
                                break;
                            end if;
                            Append(~ccRels[col],rel2);
                        end if;
                    end for;
                end for;
            end for;      
        /*ccRels created*/
            
        /*start enumeration*/
            /*apply each of the generators of H to coset 1*/
            for i in [1..#subggens] do
                apply(1, subggens[i], ~CT, true, ~ded, ~auxTab, ~POL1, ~PT, colLets, 
                    colInv, #subggens[i]+1);
            end for;
            /*main loop*/
            while lcount le llimit do
                /* lcount tracks which pass through the machine's loop this is. */
                lcount+:=1;
                if #ded gt 0 then//new entries to test
                    checkDed(~ded, ~auxTab, ~CT, ccRels, ~POL1, ~PT, colLets, colInv);
                elif (#CT gt maxrow) then//no more defs allowed, finish
                    print("maxrow reached.");
                    print "time taken:", Realtime()-start;
                    return [*colLets, CT, auxTab, PT, POL1, PT2, POL2*];        
                else//find first hole
                    hflag:=false;//true if hole found
                    //find first hole from knh
                    while knh le #auxTab and not(hflag) do
                        if auxTab[knh][2] eq 0 then//non redundant
                            col:=1;
                            while col le ncol and not(hflag) do
                                if (CT[auxTab[knh][1], col] eq 0) then
                                    hflag:=true;//hole found!
                                    break;
                                else
                                    col+:=1;
                                end if;
                            end while;
                        end if;
                        if not(hflag) then
                            knh+:=1;
                        end if;
                    end while;
                    if hflag then //hole found	
                        if (#CT le maxrow) then//fill first hole
                            if CT[auxTab[knh][1], col] eq 0 then
                                newDef(knh, col, ~CT, ~auxTab, ~PT, ~POL1, ~ded, colInv);
                            else//error
                                print "error. coset already defined";
                            end if;
                        end if;
                    else//we're done!
                        print "enumeration complete. Index=", #CT;
                        //make PT2
                        PTrow:=[[]:i in [1..ncol]];
                        PT2:=[PTrow: i in [1..#auxTab]];
                        //make POL2
                        POL2:=[[**]: i in [1..#auxTab]];
                        print "time taken:", Realtime()-start;
                        return [*colLets, CT, auxTab, PT, POL1, PT2, POL2*];
                    end if;	
                end if;
            end while;
        /*end enumeration*/
        print "Loop limit reached.";//we only get here if this is the case
        print "number of cosets made=", #auxTab;
        print "number of cosets active=", #CT;
        print "time taken:", Realtime()-start;
        return [*colLets, CT, auxTab, PT, POL1, PT2, POL2*];
    end function;
    
    /* proveWrd (prove word)
        uses L from PEACEv2 to get the proof word (stored in pfwrd) of wrd.
        pfwrd should be empty, since this would be a function except that 
        we want to be able to update PT2 and POL2, so that subsequent proofs 
        will be faster.*/
    proveWrd:=procedure(~L, wrd, ~pfwrd)
        start:=Realtime();
        colLets:=L[1];
        auxTab:=L[3];
        PT:=L[4];
        POL1:=L[5];
        ngens:=Floor(#L[1]/2);
        colInv:=[(ngens+1)..2*ngens] cat [1..ngens];
        pfwrd:=[];//set or reset input
        cos:=1;
        i:=1;
        if #wrd ne 0 then
            wrd2:=readWrd(wrd);//take out ^*() etc
            if (#wrd eq 0) then//error
                print "error: empty word argument";
            end if;
        else //error
            print "error: empty wrd";
        end if;
        wrd3:=colWrd(L[1], wrd2);
        for col in wrd3 do
            cos2:=L[2][auxTab[cos][1], col];
            tempPfwrd:=[];
            i:=1;
            while i le #L[6][cos, col] do
                if L[6][cos, col][i][1] eq cos2 then
                    tempPfwrd:=L[6][cos, col][i][2];
                    break;
                else
                    i+:=1;
                end if;
            end while;
            if #tempPfwrd eq 0 then
                pfEntry(col,cos,cos2,~L, colInv);
                tempPfwrd:=L[6][cos, col][#L[6][cos, col]][2];
            end if;
            pfwrd:=redCat(pfwrd, tempPfwrd);
            cos:=cos2;
        end for;
        print "simp1(pfwrd)=",simp1(pfwrd);
        print "simp2(pfwrd)=",simp2(pfwrd); 
        print "cos=", cos;
        print "time taken=", Realtime()-start;
    end procedure;

    /*cosDef (coset definition)
        gives the definition of the coset cos, 
        that is the word in the generators of G that give cos*/
    forward cosDef;
    cosDef:=function(cos, L)
        auxTab:=L[3];
        colLets:=L[1];
        if cos eq 1 then
            return "1";
        end if;
        str:="";//return value
        if auxTab[cos][3] ne 1 then//find definition of the coset cos was defined from
            str:=cosDef(auxTab[cos][3], L);
        end if;
        str cat:=colLets[auxTab[cos][4]];
        //add the generator used to get cos from auxTab[cos][3]
        return str;
    end function;

    /*allDefs (all definitions)
        finds coset definitions for each active coset. This can be used to
        give an exhaustive list of representatives of each element of the 
        quotient group*/
    allDefs:=function(L)
        labels:=[];//return value
        for cos in [1..#L[3]]do
            if L[3][cos][1] gt 0 then//not redundant
                Append(~labels, cosDef(cos,L));
            end if;
        end for;
        return labels;
    end function;

    /*findCos (find coset)
        find the coset number of the coset wrd*H*/
    findCos:=function(wrd, L)
        wrd2:=readWrd(wrd);
        wrd3:=colWrd(L[1], wrd2);//formatted wrd
        cos:=1;//return value
        for col in wrd3 do
            cos:=L[2][L[3][cos][1], col];//next coset
        end for;
        return cos;
    end function;

    /*Lprint (L print)
        pretty print the information from PEACEv2*/
    Lprint:=procedure(L)
        ncols:=#L[1];
        print "colLets=", L[1];
        print "CT=";
        i:=1;//index in L[3]
        while i le #L[3] do
            while i le #L[3] and L[3][i][1] eq 0 do//i is a redundant coset
                i+:=1;
            end while;
            if i le #L[3] then
                print " ", i, " ", L[2][L[3][i][1]];
            end if;
            i+:=1;
        end while;
        print "auxTab=";
        print L[3];
        print "PT=";
        for i in [1..#L[4]] do
            print " ", i, "[";
            for j in [1..ncols] do
                print "     ", L[1][j], "   ", L[4][i][j];
            end for;
        end for;
        print "POL1=";
        for i in [1..#L[5]] do
            print " ", i, " ", L[5][i];
        end for;
        print "PT2=";
        for i in [1..#L[6]] do
            print " ", i, "[";
            for j in [1..ncols] do
                print "     ", L[1][j], "   ", L[6][i][j];
            end for;
        end for;
        print "POL2=";
        for i in [1..#L[7]] do
            print " ", i, " ", L[7][i];
        end for;
    end procedure;

/*end user functions*/
