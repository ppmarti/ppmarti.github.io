# 22/4/00  2/6/05  (gap4 version, with Brauer)
# PPM's GAP Ramified Partitions macros

#{{{ 0. Standard partition algebra technology. 

# 0. Standard partition algebra technology. 
#{{{ abbreviations/set partitions Pa(S)


Pa := function(n)
    return PartitionsSet(n);
end;
Pak := function(n,k)
    return PartitionsSet(n,k);
end;

# USAGE:
# Sets can be given in the form [1,2,3]
# hence
# > Pa([1,2,3,4]);

#}}}
#{{{ PaB(S) Brauer subset of partitions

# select brauer subset from Pa(n)

PaB := function(n)
  local brauer,i,j,k,l;
  brauer:=[];
  for i in Pa(n) do
    l:=0;
    for j in i do
      k:=Length(j);
#      Print(k,j);
      if k=2 then
#        return 1;
      else
        l:=1;
#        return 0;
      fi;
    od;
    if l=0 then
      Append(brauer,[i]);
    fi;
  od;
  return brauer;
end;

# USAGE:    gap> PaB([1,2,3,4]);

#}}}
#{{{ Kaa(n) etc polygon decompositions

# Kaa(n) outputs all diagonals of an n-gon

Kaa := function(n)
  local diags,fred,i,j,k;
  diags:=[];
  for i in [1..n-2] do
    for j in [2..n-2] do
      if i+j < n+1 then
        Append(diags,[[i,i+j]]);
      fi;  
    od;
  od;
  return diags;
end;

# Check to see if set x of diagonals in polygon is non-crossing

Dgood := function(x)
  local p,q,test;
  test:=1;
  for p in x do
    for q in x do
      if ((( q[1] in [p[1]+1..p[2]-1] ) and (not( q[2] in [p[1]..p[2]] )))   
          or ((not( q[1] in [p[1]..p[2]] )) and (( q[2] in [p[1]+1..p[2]-1] ))))
         then 
        return 0;
      fi;
    od;
  od;
  return 1;
end;


Baur := function(n,m)
  # Give all angulations of n-gon (with m diagonals)
  local x,p,q,i,j,k,power,polygonset,test;
  polygonset:=[];
  power:=Combinations(Kaa(n),m);
  for x in power do
    if Dgood(x)=1 then
      Append(polygonset,[x]);
    fi;
  od;
  return polygonset;
end;

#}}}
#{{{ chat
# next: keep only one representative of angulations agreeing outside
#       their triangulated part.
# 1. determine "integer partition" Ipart(ang) of a given angulation ang.
#  i.e. number of each kind of r-gon in it. 
#  Ideas: 
#  1.1 each ang has at least one vertex with no diagonal. Then we can remove the associated r-gon without changing the rest of the story. So define a function that takes an ang as input, finds its highest such vertex; finds all the successive vertices in the corresp r-gon; then finds the angx with this r-gon removed. Iterate to find Ipart(ang).
# 2. when are two angulations Scott-equivalent?
# 3. ...

#Flat := function(ang)
# exists! flatten a partition to the underlying set

#{{{ try1

Reduceangx := function(ang,n)
  # inputs are n-gon angulation data ang and n-gon size n
  # output will be angx, ang with an `ear' removed
  local i,j,k,x,y,uset,test,start,last;
  if ang=[] then 
    return [n,1];
  fi;
  # first we look for a removable r-gon of ang
  uset := Flat(ang);
  test := 0;
  last:=1;
  # now we start going through the vertices from the highest
  for i in [n,n-1..1] do
    # Print(i);
    if test=1 then 
      if i in uset then
        # if we got here then we reached the end of a removable r-gon
        # so it is time to spit out the last, i.e. previous, vertex value
        last:=i+1;
        break;
      fi;
    fi;
    if not (i in uset) then 
      # if we got here then vertex i is in a removable r-gon
      if test=0 then 
        start:=i;
        test:=1;
      fi;
    fi;
  # note that if we finished for before last:= then last=1 (already set)
  od;
  return [start,last];
end;

#}}}
#{{{ Shrinkang Reduceang

Shrinkang := function(ang,n,set)
  # input angulation of n-gon,n, and set of consecutive vertices defining ear
  # output ang of n-|set|-gon with ear removed, and new rank
  local i,j,k,size,angx;
  angx:=[];
  size:=Size(set);
  for i in ang do
    if (i[1]+1 in set) and (i[2]-1 in set) then
      continue;
    fi;
    # renumber vertices beyond ear
    if i[1]>set[1] then
      j:=i[1]-size;
      k:=i[2]-size;
    else
      if i[2]>set[1] then
        j:=i[1];
        k:=i[2]-size;
      else
        j:=i[1];
        k:=i[2];
      fi;
    fi;
    Append(angx,[[j,k]]);
  od;
  return [angx,n-size];
end;
  
Reduceang := function(angn)
  # inputs are n-gon angulation data ang and n-gon size n
  # output will be angx, = ang with an `ear' r-gon removed; and r
  # 1st step is just to find an ear r-gon, so we look for a bare vertex
  # then the bare vertices around it
  # or a non-bare vertex then the first bare one after that
  # then the run of bare vertices from there
  local i,j,k,short,x,y,uset,ang,n,notbare,test,start,last,poly,angx;
  # if ang=[] then no non-bare vertex, so do this case now:
  ang:=angn[1];
  n:=angn[2];
  if ang=[] then 
    # should not ever get here!
    Print(999);
    return [n,1];
  fi;
  # first we look for a removable r-gon of ang
  # we start with some non-bare vertex and work round looking for a
  # first bare one
  ##  notbare:=ang[1][1];
  # (but there are problems with this!!!)
  # OR, we look through for a `shortest' diagonal
  short:=ang[1];
  for i in ang do
    if (i[2]-i[1]) < (short[2]-short[1]) then
      short:=i;
    fi;
  od;
  notbare:=short[1];
  uset := Flat(ang);
  test := 0;
  poly:=[];
  last:=1;
  # now we start going through the vertices from the initial nonbare one
  for i in [1..n-1] do
    if (notbare+i in uset)  then
      if test=0 then
        continue;
      else
        break;
      fi;
    else 
      test:=1;
      Append(poly,[notbare+i]);
    fi;
  od;
  #  return poly;
  angx:=Shrinkang(ang,n,poly);
  #  Print(angx);
  return [poly,angx];
end;

#}}}
#{{{ Baurtab

Baurtab := function(n,m)
  # input n,m for n-gon angulations ang with m edges
  # output a sequence of the r-gons in each ang
  local ang,angx,i,j,k,tab,ear,tabby,count,countx;
  tab:=[];
  tabby:=[0,0,0,0,0,0,0,0,0,0];
  count:=[0,0,0];
  countx:=0;
  for ang in Baur(n,m) do
    tab:=[];
    tabby:=[0,0,0,0,0,0,0,0,0,0];
    angx:=[ang,n];
    ##Print(angx);
    # now start reducing ang, until  no edges left
    while not (angx[1]=[]) do
      ##Print(angx[1]);
      ear:=Reduceang(angx)[1];
      angx:=Reduceang(angx)[2];
      #      Print(Reduceang(angx));
      Append(tab,[Size(ear)+2]);
      tabby[Size(ear)+2]:= tabby[Size(ear)+2]+1;
    od;
    Append(tab,[angx[2]]);
    tabby[angx[2]]:=tabby[angx[2]]+1;
    countx:=countx+1;
    if tabby=[0,0,3,0,1,0,0,0,0,0] then
      count[1]:=count[1]+1;
    fi;
    if tabby=[0,0,1,1,1,0,0,0,0,0] then
      count[2]:=count[2]+1;
    fi;
    if tabby=[0,0,2,2,0,0,0,0,0,0] then
      count[3]:=count[3]+1;
    fi;
    Print(tab,tabby,count,countx,"\n");
  od;
end;


#}}}
#{{{ Baurtabb

Baurtabb := function(n,m,reftab)
  # Input n,m for n-gon angulations ang with m edges; 
  # and a reference partition reftab, where
  # reftab=[t_1, t_2, t_3, t_4, ..., t_10] means t_r r-gons. (NB r<11!!!)
  # Output a sequence of the r-gons in each ang  matching partition reftab. 
  local ang,angx,i,j,k,tab,ear,tabby,count,countx;
  tab:=[];
  tabby:=[0,0,0,0,0,0,0,0,0,0];
  count:=[0,0,0];
  countx:=0;
  for ang in Baur(n,m) do
    tab:=[];
    tabby:=[0,0,0,0,0,0,0,0,0,0];
    angx:=[ang,n];
    ##Print(angx);
    # now start reducing ang, until  no edges left
    while not (angx[1]=[]) do
      ##Print(angx[1]);
      ear:=Reduceang(angx)[1];
      angx:=Reduceang(angx)[2];
      #      Print(Reduceang(angx));
      Append(tab,[Size(ear)+2]);
      tabby[Size(ear)+2]:= tabby[Size(ear)+2]+1;
    od;
    Append(tab,[angx[2]]);
    tabby[angx[2]]:=tabby[angx[2]]+1;
    countx:=countx+1;
    if tabby=reftab then
      count[1]:=count[1]+1;
    fi;
    if tabby=[0,0,1,1,1,0,0,0,0,0] then
      count[2]:=count[2]+1;
    fi;
    if tabby=[0,0,2,2,0,0,0,0,0,0] then
      count[3]:=count[3]+1;
    fi;
    Print(tab,tabby,count,countx,"\n");
  od;
end;


#}}}
#}}}
#{{{ duff stuff

Minifacefinder := function(ang,i,n)
  # find face {i,i+1,...} in n-gon angulation ang
  # (don't forget not every face is of this form!)
  local x,y,j,angpair,face;
  face := [i,i+1];
  # where is next edge after [i,i+1]? it is highest  number edge out of i+1
  # (if any). so find all edges out of i+1:
  angpair := [];
  for j in [1..n] do
    if ( [i,j] in ang ) then 
      Append(angpair,[j]);
    fi;
  od;
  Print(angpair);
  if angpair=[] then
    Append(face,[i+2]);
  fi;
  return face;
end;

        
#}}}

#}}}





#{{{ local vars


# Local Variables:
# mode: Gap
# folded-file: t 
# fold-top-mark : "#{{{"
# fold-bottom-mark : "#}}}"
# End:

#}}}




