/// Time-0.080s

/// It's solution is already in my sparse-table repository using only LCA 
/// Here , I used HLD algorithm

#include <bits/stdc++.h>

using namespace std;

struct edge {
    int v, w, idx;
};

const int N = 100001, L = 21;
int test, vertex;
int Maxlog;
vector <edge> G[N];
int sparse[L][N], Lev[N], tree[N << 2], two[L];
int chainNo;///It hold the chain number
int  chainHead[N], chainSize[N];///chainHead[i] holds the first node of the ith chain.
int nodeInWhichChain[N];/// nodeInWhichChain[i] ,find the chain number,in which the node i situated
int  indexInBaseArray[N];/// indexInBaseArray[i],the position in base-array of node i
int BaseArray[N];/// this is our original array ,which have been used in segment tree for updating ,querying .
int indexNo;/// it is the index of base array
int edgeIndex[N];/// It hold the position of the ith edge in base array
int subtreeSize[N];/// It is used for the subtree size of every node

void dfs(int u , int par , int level ) {
    sparse[0][u] = par;
    Lev[u] = level;
    subtreeSize[u] = 1;
    for (int i = 0; i < (int) G[u].size(); i++) {
        int v = G[u][i].v;
        if (v != par) {
            dfs(v, u, level + 1);
            subtreeSize[u] += subtreeSize[v];
        }
    }
}

/// building sparse-table for finding lca
void sparseTable() {
    for (int i = 1; two[i] <= vertex; i++) {
        for (int j = 1; j <= vertex; j++) {
            if (sparse[i - 1][j] != -1) { /// if 2^(i-1) th ancestor of jth node is available then proceed
                sparse[i][j] = sparse[i - 1][sparse[i - 1][j]];
            /// sparse[i][j] states for 2^ith node from j node
            }
        }
    }
}

void hld(int node , int par , int cost ) {
    indexNo++;/// It indicates the length of base array
    indexInBaseArray[node] = indexNo;
    BaseArray[indexNo] = cost;/// Base array holds the cost of edges
    if (chainHead[chainNo] == -1) chainHead[chainNo] = node;
    nodeInWhichChain[node] = chainNo;
    chainSize[chainNo]++;
    int specialChild = -1, maxSubtreeSize = -1;
    int specialCost, specialIndex;

    for (int i = 0; i < (int) G[node].size(); i++) {
        int v = G[node][i].v, w = G[node][i].w;
        int idx = G[node][i].idx;
        if (v != par && subtreeSize[v] > maxSubtreeSize) {
            maxSubtreeSize = subtreeSize[v];
            specialChild = v, specialCost = w;
            specialIndex = idx;
        }
    }

    /// expanding chain's length
    if (specialChild != -1) {
        /// It hold the position of the ith edge in base array.
        edgeIndex[specialIndex] = indexNo + 1;
        hld(specialChild, node, specialCost);
    }

    /// linking chain from normal nodes
    for (int i = 0; i < (int) G[node].size(); i++) {
        int v = G[node][i].v, w = G[node][i].w;
        int idx = G[node][i].idx;
        if (v != par && v != specialChild) {
            chainNo++;
        /// It hold the position of the ith edge in base array.
            edgeIndex[idx] = indexNo + 1;
            hld(v, node, w);
        }
    }
}

/// construction of segment tree from base-array
void build(int lo , int hi, int node) {
    if (lo == hi) {
        tree[node] = BaseArray[lo];
        return;
    }
///left=2*node ,right = left +1,to add 1 to a even number can be done by bit ,here  left|1 = left+1 ,as left is always even number .
    int mid = (lo + hi)>>1, left = node << 1, right = left | 1;
    build(lo, mid, left);
    build(mid + 1, hi, right);
    tree[node] = (tree[left]+tree[right]);
}


/// Time-Complexity O(logn)
int get(int x, int y, int lo , int hi, int node ) {
    /// outside range so return 0,as we are finding max number in range
    if (lo > hi || y < lo || hi < x) return 0;
    /// In range ,so return value from tree .
    if (x <= lo && hi <= y) return tree[node];
    /// left=2*node , right = left +1 , to add 1 to a even number can be done by bit ,here  left|1 = left+1 ,as left is always even number .
    int mid = (lo + hi) >>1, l = node << 1, r = l | 1;
    int le = get(x, y, lo, mid, l);
    int ri = get(x, y, mid + 1, hi, r);
    return (le+ri);
}

void build_hld() {
    indexNo = 0, chainNo = 1;
    for (int i = 1; i <= vertex; i++) {
        chainHead[i] = -1;
       /// chainSize[i] = -1;
    }
    /// initialize all values of sparse table
    for (int i = 0; two[i] <= vertex; i++) {
        for (int j = 1; j <= vertex; j++)
            sparse[i][j] = -1;
    }
    dfs(1,-1,0);/// root , parent,level
    sparseTable();
    hld(1,-1,0);///root,parent,cost
    build(1,vertex,1);/// start,end,root
}

/// finding lca of a and b
int lca(int a, int b)
    {
        if(Lev[a]>Lev[b]) {swap(a,b);}

        int dif_between_lev=Lev[b]-Lev[a];
        /// we have to find out the same level of a which is also ancestor of b
        while(dif_between_lev>0) /// if difference between b and a is above zero , we can reduce it by binary lifting
        {
            int max_mum_power_of_i=log2(dif_between_lev);
            ///b=sparse[b][max_mum_power_of_i];
            b=sparse[max_mum_power_of_i][b];
            dif_between_lev-=(1<<max_mum_power_of_i);
        }
        if(b==a) return b;/// if a is itself ancestor of a and b

 ///Now,two are on same level,so trying to reduce the level  just before that ancestor node
        for(int i=Maxlog;i>=0;i--)
        {
            if(sparse[i][a]!=-1 && sparse[i][a]!=sparse[i][b])
            {
                a=sparse[i][a];
                b=sparse[i][b];
            }
        }
        return sparse[0][a];/// sparse[a][0] , now print the just parent of this node
    }

    /// This will return kth node from a to b , not from b to a be careful about this. kth node from a to b
    int kthnode_from_a(int a,int b,int k,int lca)
    {   /// One thing-> by binary lifting we can come up to lower level from higher level
        /// So , when a is upper level then we will find how much cover will we have to do  from b to a to find kth node from a
        /// when a is in higher level then task is half done ,we have to come up from higher level of a to (lower level) kth node
        /// But when node structure will be like a-------(lca)------b ,then by binary lifting we will not be able to pass lca to go to (lca -> b) path
        /// So, then with some calculation  we will go from b to lca , to find desire node which is kth from a
        /// Let's start
        int total_nodes_between_a_and_b;
        if(lca==a) /// a node itself is lca of a and b node ,so a is upper level we have to swap it as we will go all time from higher level to lower level
        {
            total_nodes_between_a_and_b=Lev[b]-Lev[a]+1;
            swap(a,b);
            k=total_nodes_between_a_and_b-k+1;///  this is now new k ,as we swap a and b
        }
        else if(lca==b);/// then a is on higher level and lca is q ,so only by binary lifting we can come up to kth node ,no need extra calculation

        else ///  when node structure will be like a-------(lca)------b , lca is neither a nor b but a middle node of path from a to b
        {
             if(Lev[a] - Lev[lca] + 1 < k) ///when kth node is on the path (lca->b), then we need some calculations as we have to go to desire node from b node ,not from a node
            {
              total_nodes_between_a_and_b = Lev[a] + Lev[b] - 2 * Lev[lca] + 1;
              k = total_nodes_between_a_and_b - k + 1;
              swap(a,b);/// as we will start our binary lifting journey from b to a ,so swap (a,b)
            }
        }
        /// because k is numbered from a ,where a itself is 1st node from a ,so decrease k one
        k--;
        /// three cases has been checked and new k has been calculated  ,now to use binary lifting finally to find kth node from a
         int desire_jump=k;
        /// we have to find out the same level of a which is also ancestor of b
        while(desire_jump>0) /// if difference between b and a is above zero , we can reduce it by binary lifting
        {
            int max_mum_power_of_i=log2(desire_jump);
            a=sparse[max_mum_power_of_i][a];
            desire_jump-=(1<<max_mum_power_of_i);
        }
        return a;
    }


/// Assuming u is ancestor of v
/// Suppose the normal tree (u-v-a-b-c-d)
/// when we create base array then with including cost (u-v),we will denote the position of v of basearray of cost (u-v) .
/// That makes sense to us that if we want to find out the max value between node(v) to node(c)
/// Then it will compare cost of these edges( u-v , v-a , a-b, b-c )
/// But u-v should not be taken into account .
/// So , when we will see that u and v are in same chain ,then as u is ancestor so it's level is low and v's level is high
/// So we would get segment (L.....R) for finding query ,where L and R are the indexInBaseArray
/// But we have to compute ( L+1......R ) as all things are explained above .
int hldQuery(int u, int v) {
    int ret = 0;
    while (true) {
        if (nodeInWhichChain[u] == nodeInWhichChain[v]) {
        /// now node v and node u are in the same chain
            int L = indexInBaseArray[u];
            int R = indexInBaseArray[v];
            if (L < R) ret += get(L+1, R,1,vertex,1);///range(L,R) , start,end,root .
            return ret;
        }
        /// trying to make come v , into the same chain of u
        int head = chainHead[nodeInWhichChain[v]];///getting first node of the chain
        int L = indexInBaseArray[head];
        int R = indexInBaseArray[v];
        ret += get(L, R,1,vertex,1);///range(L,R) , start,end,root .
        v = sparse[0][head];///going into another chain
    }
}

int query(int x, int y) {
    int l = lca(x, y);
    return (hldQuery(l, x)+ hldQuery(l, y));
}

int main() {
    scanf("%d", & test);
    /// pre-calculate all values of 2^i ...which will be used for building sparse table
    two[0] = 1;
    for (int i = 1; i <= 20; i++)
        two[i] = two[i - 1] << 1;
    while (test--) {
        scanf("%d", & vertex);
        Maxlog=log2(vertex+1);
        for (int i = 1; i <= vertex - 1; i++) {
            int x, y, z;
            scanf("%d %d %d", & x, & y, & z);
             struct edge e;
            e.v=y;/// connected node
            e.w=z;/// edge's cost
            e.idx=i;/// serial index of the edge
            G[x].push_back(e);
            e.v=x;/// connected node
            e.w=z;/// edge's cost
            e.idx=i;/// serial index of the edge
            G[y].push_back(e);
        }
        build_hld();
        char str[10];
        while (scanf(" %s", str)) {
            if(str[0] == 'D'&& str[1]=='O'&&str[2]=='N'&&str[3]=='E') break;
            int x, y,k;
            scanf("%d %d", &x, &y);
            if (str[0] == 'D') {
                printf("%d\n", query(x, y));
            } else {
                scanf("%d",&k);
                printf("%d\n",kthnode_from_a(x,y,k,lca(x,y)));
            }
        }
        for (int i = 1; i <= vertex; i++) {
            G[i].clear();
        }
    }
}
