#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include "ranNumbers.h"

/*=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- FUNCTIONS =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*/

void genWSnet(int *edge, int *nodeDegree, int nEdges,
		int nNodes, int K, float betaWS, Ran &ranUni)
{
	int ii, jj, kk, ee, auxInt, accept;

	// Conect each node with its neighboring nodes
	for (ii=0; ii<nNodes; ii++) for (kk=0; kk<K; kk++)
	{
		jj = ii + kk + 1;
		if (jj >= nNodes) jj -= nNodes;

		auxInt = kk + ii*K;
		edge[auxInt] = jj;

		nodeDegree[ii]++;
		nodeDegree[jj]++;
	}

	if (betaWS == 0.0) return;

	// Rewire the edges
	for (ee=0; ee<nEdges; ee++)
	{
		ii = ee/K;
		jj = edge[ee];

		if (betaWS < 1.0)
			if (ranUni.doub() >= betaWS) continue; // Doesn't rewire

		nodeDegree[jj]--;
		accept = 0;
		while (!accept)
		{
			jj = ranUni.int32()%nNodes;
			if (jj == ii) continue; // avoid self-loop

			// Find if the edge already exists
			for (kk=0; kk<K; kk++)
			{
				auxInt = kk + ii*K;
				if (edge[auxInt] == jj) break;
				auxInt = kk + jj*K;
				if (edge[auxInt] == ii) break;
				if (kk == K-1) accept = 1; // Accept the edge
			}
		}

		edge[ee] = jj; // Rewire with the new node
		nodeDegree[jj]++;
	}

	return;
}

//---------------------------------------------------------------------------------//

void genBAnet(int *edge, int *nodeDegree, int nNodes, int K, Ran &ranUni)
{
	int ii, jj, kk, auxInt;

	// Complete graph with the 2K+1 first nodes
	int initNodes = 2*K + 1;
	for (ii=0; ii<initNodes; ii++) for (kk=0; kk<K; kk++)
	{
		jj = ii + kk + 1;
		if (jj >= initNodes) jj -= initNodes;

		auxInt = kk + ii*K;
		edge[auxInt] = jj;

		nodeDegree[ii]++;
		nodeDegree[jj]++;
	}

	int *bagIds, lenBagIds;
	lenBagIds = (nNodes - initNodes)*(K+1) + initNodes;
	bagIds = (int*) malloc(lenBagIds*sizeof(int));
	for (ii=0; ii<initNodes; ii++) bagIds[ii] = ii; // Collect the initial nodes in the bag
	for (ii=initNodes; ii<lenBagIds; ii++) bagIds[ii] = -1;

	// Connect each new node to previous nodes with
	// a probability dependent on their degrees
	int ee, bb, accept, trial;
	int countIds;
	countIds = initNodes;
	bb = initNodes;
	for (ii=initNodes; ii<nNodes; ii++)
	{
		for (kk=0; kk<K; kk++)
		{
			accept = 0;
			while (!accept)
			{
				trial = ranUni.int32()%countIds;

				jj = bagIds[trial];
				if (jj == ii) continue;

				if (kk == 0) accept = 1; // Accept the edge

				// Find if the edge already exists
				for (ee=0; ee<kk; ee++)
				{
					auxInt = ee + ii*K;
					if (edge[auxInt] == jj) break;
					if (ee == kk-1) accept = 1; // Accept the edge
				}
			}

			ee = kk + ii*K;
			edge[ee] = jj; // Save the edge
			nodeDegree[ii]++;
			nodeDegree[jj]++;
			bagIds[bb++] = jj; // Collect the index of the node jj
		}

		bagIds[bb++] = ii;
		countIds += K + 1;
	}
	free(bagIds);

	return;
}

//---------------------------------------------------------------------------------//

void swap(int &i, int &j)
{int dum = i; i = j; j = dum;}

void quickSort(int *arrIdx, int *arrKey, int size)
{
	// M is the size of subarrays sorted by insertion methods
	// nStack is the required aux storage
	static const int M = 7, nStack = 64;

	int i, ir, j, k, jStack=-1, l=0, n=size;
	int a;
	ir = n-1;
	int *iStack;
	iStack = (int*) malloc(nStack*sizeof(int));
	while (1)
	{
		if (ir-l < M)
		{
			for (j=l+1; j<=ir; j++)
			{
				a = arrIdx[j];
				for (i=j-1; i>=l; i--)
				{
					if (arrKey[arrIdx[i]] >= arrKey[a]) break;
					arrIdx[i+1] = arrIdx[i];
				}
				arrIdx[i+1] = a;
			}

			if (jStack < 0) break;
			// Begin a new round of partitioning
			ir = iStack[jStack--];
			l = iStack[jStack--];
		}
		else
		{
			// Choose median as partitioning element a
			k = (l + ir) >> 1; // Binary right shift operator (1 place is a int division by 2)
			swap(arrIdx[k], arrIdx[l+1]);
			// Rearrange for arrIdx[l] >= a[l+1] >= a[ir] 
			if (arrKey[arrIdx[l]] < arrKey[arrIdx[ir]])
				swap(arrIdx[l], arrIdx[ir]);
			if (arrKey[arrIdx[l+1]] < arrKey[arrIdx[ir]])
				swap(arrIdx[l+1], arrIdx[ir]);
			if (arrKey[arrIdx[l]] < arrKey[arrIdx[l+1]])
				swap(arrIdx[l], arrIdx[l+1]);

			// Initialize pointers for partitioning
			i = l+1;
			j = ir;
			a = arrIdx[l+1]; // partitioning element

			// Change elements < a to the right and elements > a to the left
			while(1)
			{
				do i++; while (arrKey[arrIdx[i]] > arrKey[a]);
				do j--; while (arrKey[arrIdx[j]] < arrKey[a]);
				if (j < i) break;
				swap(arrIdx[i], arrIdx[j]);
			}
			arrIdx[l+1] = arrIdx[j]; // Insert partitioning element
			arrIdx[j] = a;
			jStack += 2;

			// Push pointers to larger subarray on stack.
			// Process smaller subarray inmediately.
			if (jStack >= nStack) {printf("nStack too small\n"); exit(2);}
			if (ir-i+1 >= j-1)
			{
				iStack[jStack] = ir;
				iStack[jStack-1] = i;
				ir = j-1;
			}
			else
			{
				iStack[jStack] = j-1;
				iStack[jStack-1] = l;
				l = i;
			}
		}
	}

	free(iStack);
	return;
}

//---------------------------------------------------------------------------------//
void epiSimulation(int *newI_vec, short *nodeStatus, short *nodeInfec,
                int *expTimeNode, int *infecTimeNode,
                int K, float probInfec, float probDevInfec, float probRandomLD,
                int nNodes, int nEdges, int *edge, int initInfec, int maxDays,
                int flagActLD, int ldStart, int ldEnd, int interval, Ran &ranUni)
{
	// Status (SEAIR: Susceptible, Exposed, Asymptomatic, Infected, Removed)
        // 0:S, 1:E1, 2:A1, 3:I1, 4:R1, -1:E2, -2:A2, -3:I2, -4:R2
        memset(nodeStatus, 0, nNodes*sizeof(short)); // All nodes are susceptibles
        memset(nodeInfec, 0, nNodes*sizeof(short));

	int nn;
        int nContagious;
        int nSuscep, nExpo, nAsymp, nInfec, nRem;
        int nExpo2, nAsymp2, nInfec2, nRem2;
        int newE, newA, newI, newR, newE2, newA2, newI2, newR2, oldI, daysNewI;
        short iiStatus, jjStatus;

        nSuscep = nNodes;
        nExpo = 0;
        nAsymp = 0;
        nInfec = 0;
        nRem = 0;
        nExpo2 = 0;
        nAsymp2 = 0;
        nInfec2 = 0;
        nRem2 = 0;

        newE = 0;
        newA = 0;
        newI = 0;
        newR = 0;
        newE2 = 0;
        newA2 = 0;
        newI2 = 0;
        newR2 = 0;
        oldI = 0;
        daysNewI = 0;

        // Choosing random node for Infected status
        for (nn=0; nn<initInfec; nn++)
        {
                auxInt = ranUni.int32()%nNodes;
                while (nodeStatus[auxInt] != 0) auxInt = ranUni.int32()%nNodes;
                nodeStatus[auxInt] = 3; // Infected
                nSuscep--;
                nInfec++;
                newI++;
        }

        short flagLockdown, flagVariant2, switchLD, flagVacc, count, countV;
        int time, timeLD, idxV, sumI, sumI2;
        float auxF;

        flagVariant2 = 0;
        flagLockdown = 0;
        switchLD = 0;
        count = 0;
        countV = 0;
        time = 0;
        timeLD = 0;
	idxV = 0;
        flagVacc = 0;
        sumI = 0;
        sumI2 = 0;

        while (1)
        {
                nContagious = nExpo + nAsymp + nInfec + nExpo2 + nAsymp2 + nInfec2;

                sumI += newI;
                sumI2 += newI2;

                time++;
                if (time > maxDays) break;
		
		// Activate lockdown and/or vaccination
		if (flagActLD or flagActVacc)
			if (!flagLockdown or !flagVacc)
			{
				if (newI + newI2 > oldI) daysNewI++;
                		else daysNewI = 0;
                		oldI = newI + newI2;
			}

		// Lockdown
                if (flagActLD and !flagLockdown)
                        if (daysNewI > ldStart)
                        {
                                flagLockdown = 1; // Activate lockdown once
                                switchLD = 1;
                        }

                if (flagLockdown == 1)
                {
                        if (interval > 0)
                        {
                                count++;
                                if (count > interval)
                                {
                                        count = 0;
                                        if (switchLD) switchLD = 0;
                                        else switchLD = 1;
                                }
                        }

                        timeLD++;
                        if (timeLD > ldEnd)
                        {
                                flagLockdown = 2;
                                switchLD = 0;
                        }
                }

		// Vaccination
                if (flagActVacc and !flagVacc)
                        if (daysNewI > vaccStart)
                        {
                                flagVacc = 1; // Activate vaccination
                                if (vaccPerDay == 0) flagVacc = -1; // Deactivate vaccination
                        }

                // Vaccinates Susceptible nodes
                if (flagVacc == 1)
                {
                        nn = 0;
                        while (nn<vaccPerDay)
                        {
                                if (idxV == nNodes) break;
                                auxInt = vaccOrder[idxV];
                                idxV++;
                                if (nodeStatus[auxInt] != 0) continue;
                                nodeStatus[auxInt] = 10;
                                nn++;
                                vaccGoal--;
                                if (vaccGoal == 0) break;
                        }
                        if (vaccGoal == 0) flagVacc = 3;
                        if (idxV == nNodes) flagVacc = 3;
                }

		// Restart counts
                newE = 0;
                newA = 0;
		newI = 0;
                newR = 0;
                newE2 = 0;
                newA2 = 0;
                newI2 = 0;
                newR2 = 0;

                if (nContagious == 0)
                {
                        if (variant2Intro == 0.0) break;
                        if (flagVariant2 == 1) break;
                        if (time < variant2Intro) continue;
                }

		// Finds a Susceptible (0) node and infects it with variant 2
                if (time == variant2Intro)
                {
                        flagVariant2 = 1;
                        for (nn=0; nn<initInfec; nn++)
                        {
                                auxInt = ranUni.int32()%nNodes;
                                while (nodeStatus[auxInt] != 0) auxInt = ranUni.int32()%nNodes;
                                nodeStatus[auxInt] = -3; // Infected
                                nSuscep--;
                                nInfec2++;
                                newI2++;
                        }
                }

		
                // Identifies the suceptible nodes and determine if they will be infected
                for (ee=0; ee<nEdges; ee++)
                {
                        // Lockdown resriction
                        if (switchLD) if(edgeLD[ee] == 0) continue;

                        ii = ee/K;
                        jj = edge[ee];

                        iiStatus = nodeStatus[ii];
                        jjStatus = nodeStatus[jj];

			switch (iiStatus)
			{
				case 0:
					flagS = 1;
					prob = probInfec1;
					break;

				case 10:
					flagS = 1;
					prob = probInfec1;
					break;

				case 11:
					flagS = 1;
					prob = 1d_ineff*probInfec1;
					break;

				case 12:
					flagS = 1;
					prob = 2d_ineff*probInfec1;
					break;

				default:
					flagS = 0;
					break;
    			}

                        if (flagS) // Susceptible
                        {
				// Variant 1
                                if (jjStatus == 2 or jjStatus == 3) 
                                {
                                        if (ranUni.doub() <= prob) nodeInfec[ii] = 1;
                                }
				
				// Variant 2
                                if (jjStatus == -2 || jjStatus == -3)
				{
					if (ranUni.doub() <= probInfec2) nodeInfec[ii] = -1;
				}
                        }

                        if (iiStatus == 4) // Removed 1
                        {
                                if (jjStatus == -2 || jjStatus == -3) if (ranUni.doub() <= probInfec2) nodeInfec[ii] = -1;
                        }

			flagS = 0;

                        if (jjStatus == 0) // Susceptible
                        {
                                auxInt = vaccStatus[jj];

				// Variant 1
                                if (iiStatus == 2 or iiStatus == 3) 
                                {
                                	if (auxInt == 1) auxF = ineff1; // Vaccinated with one dose
					else if (auxInt == 2) auxF = ineff2; // Vaccinated with two doses
					else auxF = 1.0;

                                        if (ranUni.doub() <= auxF*probInfec1) nodeInfec[jj] = 1;
                                }

				// Variant 2
                                if (iiStatus == -2 || iiStatus == -3)
				{
					if (ranUni.doub() <= probInfec2) nodeInfec[jj] = -1;
				}
                        }

                        if (jjStatus == 3) // Removed 1
                        {
                                if (iiStatus == -2) if (ranUni.doub() <= probInfec2) nodeInfec[jj] = -1;
                        }

                }

                // Update states
                for (ii=0; ii<nNodes; ii++)
                {
                        // Update status of the vaccination
                        if (vaccStatus[ii] == 1)
                        {
                                vaccTime[ii]--;
                                if (vaccTime[ii] == 0) vaccStatus[ii] = 2; // booster
                        }

                        iiStatus = nodeStatus[ii];

                        if (iiStatus == 0) // Suceptible
                        {
                                if (nodeInfec[ii] == 1)
                                {
                                        nodeStatus[ii] = 1;
                                        nSuscep--;
                                        nExpo++;
                                        newE++;
                                }

                                if (nodeInfec[ii] == -1)
                                {
                                        nodeStatus[ii] = -1;
                                        nSuscep--;
                                        nExpo2++;
                                        newE2++;
                                }
                                nodeInfec[ii] = 0;
                                continue;
			}

                        if (iiStatus == 1) // Exposed 1
                        {
                                expTimeNode[ii]--;
                                if (expTimeNode[ii] > 0) continue;
                                if (ranUni.doub() <= probDevInfec)
                                {
                                        nodeStatus[ii] = 2; // Infected
                                        nExpo--;
                                        nInfec++;
                                        newI++;
                                }
                                else
                                {
                                        nodeStatus[ii] = 3; // Removed
                                        nExpo--;
                                        nRem++;
                                        newR++;
                                }
                                expTimeNode[ii] = gammaE.dev();
                                continue;
                        }

                        if (iiStatus == -1) // Exposed 2
                        {
                                expTimeNode[ii]--;
                                if (expTimeNode[ii] > 0) continue;
                                if (ranUni.doub() <= probDevInfec)
                                {
                                        nodeStatus[ii] = -2; // Infected 2
                                        nExpo2--;
                                        nInfec2++;
                                        newI2++;
                                }
                                else
                                {
                                        nodeStatus[ii] = -3; // Removed 2
                                        nExpo2--;
                                        nRem2++;
                                        newR2++;
                                }
                                continue;
                        }

                        if (iiStatus == 2) // Infected 1
                        {
                                infecTimeNode[ii]--;
                                if (infecTimeNode[ii] > 0) continue;
                                nodeStatus[ii] = 3; // Removed
                                nInfec--;
                                nRem++;
                                newR++;
                                infecTimeNode[ii] = gammaI.dev();
                                continue;
                        }

			if (iiStatus == -2) // Infected 2
                        {
                                infecTimeNode[ii]--;
                                if (infecTimeNode[ii] > 0) continue;
                                nodeStatus[ii] = -3; // Removed 2
                                nInfec2--;
                                nRem2++;
                                newR2++;
                                continue;
                        }

                        if (iiStatus == 3) // Removed 1
                        {
                                if (nodeInfec[ii] == -1)
                                {
                                        nodeStatus[ii] = -1;
                                        nRem--;
                                        nExpo2++;
                                        newE2++;
                                }
                                nodeInfec[ii] = 0;
                                continue;
                        }

                }
	}

	return;
}


/*=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- MAIN =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*/

int main()
{
	//===| PARAMETERS |===//
	short err_flag = 0;
	long seed;
	int netModel, aveD, initInfec, ldStart, ldEnd, interval, variant2Intro, maxDays,
	    numSims, flagActLD, flagActVacc, flagOrderDegree, flagInitVacc, vaccStart;
	float xNodes, betaWS;
	float probRandomLD, probInfec1, probInfec2, probDevInfec, vaccFrac, vaccPerDayFrac;
	float 1d_vaccEff, 2d_vaccEff;
	char renglon[200];

	// Number of nodes
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &xNodes);

	// Network model (0: Watts-Strogatz 1: Barabasi-Albert)
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &netModel);

	// Average degree of nodes
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &aveD);

	// Probability of rewired (WS)
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &betaWS);

	// Initial infected nodes
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &initInfec);

	// Introduction of the variant 2
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &variant2Intro);

	// Probability of developing infection
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &probDevInfec);

	// Probability of infecting with variant 1
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &probInfec1);

	// Probability of infecting with variant 2
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &probInfec2);

	// Maximum number of days to simulate
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &maxDays);

	// Nnumber of simualtions (replicates)
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &numSims);

	// Seed for random number
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%ld", &seed);

	// Space
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;

	// Lockdown?
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &flagActLD);

	// Probability to restrict en edge during the LD
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &probRandomLD);

	// Start of lockdown
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &ldStart);

	// End of lockdown
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &ldEnd);

	// Lockdown interval
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &interval);

	// Space
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;

	// Vaccination?
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &flagActVacc);

	// Order by degree?
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &flagOrderDegree);

	// Vaccinate from the beginning?
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &flagInitVacc);

	// Start of vaccination
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &vaccStart);

	// Fraction of population to vaccinate
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &vaccFrac);

	// Fraction of population to vaccinate per day
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &vaccPerDayFrac);

	// One-dose vaccine efficacy
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &1d_vaccEff);

	// Two-dose vaccine efficacy
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &2d_vaccEff);

	if (err_flag)
	{
		printf("Parameter file error (.data)\n");
		exit (1);
	}

	// Initialize random uniform numbers
	Ran ranUni(seed);
	// In this gamma-distributed random generator a = k, b = 1/theta
	// Exposed time = 5d +- 1d
	Gammadev gammaE(25.0,5.0,seed); // a = (aveTime/stdTime)^2; b = aveTime/stdTime^2
	// Infected time = 6d +- 2d
	Gammadev gammaI(36.0/4.0,6.0/4.0,seed); // a = (aveTime/stdTime)^2; b = aveTime/stdTime^2

	char dirFile[100];
        int tt, ss, nn;
        //FILE *fNewI;

        int *edge, *edgeLD;
        short *nodeStatus, *nodeInfec;
	int *nodeDegree;
        int *expTime, *infecTime;
        int *newI_vec;

        int nNodes = xNodes;
        int K = aveD/2;
        int nEdges = K*nNodes;

        edge = (int*) malloc(nEdges*sizeof(int));
        edgeLD = (int*) malloc(nEdges*sizeof(int));
	nodeDegree = (int*) malloc(nNodes*sizeof(int));
        nodeStatus = (short*) malloc(nNodes*sizeof(short));
        nodeInfec = (short*) malloc(nNodes*sizeof(short));
        expTime = (int*) malloc(nNodes*sizeof(int));
        infecTime = (int*) malloc(nNodes*sizeof(int));

        newI_vec = (int*) malloc(maxDays*sizeof(int));

        memset(newI_vec, 0, maxDays*sizeof(int));

	int ee, ii, jj, kk;
	int auxInt;
        int halfNodes = nNodes/2;

        short *vaccTime;
        int *vaccOrder;
        int vaccGoal, vaccPerDay;
	
        float ineff1, ineff2;
	1d_ineff = 1.0 - 1d_vaccEff;
	2d_ineff = 1.0 - 2d_vaccEff;

        vaccTime = (short*) malloc(nNodes*sizeof(short));
        vaccOrder = (int*) malloc(nNodes*sizeof(int));

        vaccGoal = vaccFrac*nNodes;
       	vaccPerDay = vaccPerDayFrac*vaccGoal;

	for (ss=0; ss<numSims; ss++)
	{
		//-------- Generate networks --------//

		memset(nodeDegree, 0, nNodes*sizeof(int));

		if (netModel == 0) // Wattz-Strogatz network (ER -> beataWS = 1.0)
                	genWSnet(edge, nodeDegree, nEdges, nNodes, K, betaWS, ranUni);
        	else // Barabasi-Albert network
                	genBAnet(edge, nodeDegree, nNodes, K, ranUni);

		for (nn=0; nn<nNodes; nn++) expTime[nn] = gammaE.dev();
                for (nn=0; nn<nNodes; nn++) infecTime[nn] = gammaI.dev();

		//-------- Lockdown --------//

        	if (flagActLD) for (ee=0; ee<nEdges; ee++)
        	{
        	        if (probRandomLD > 0.0)
        	                if (ranUni.doub() > probRandomLD) edgeLD[ee] = 1;
        	                else edgeLD[ee] = 0;
        	        else
        	        {
        	                ii = ee/K;
        	                jj = edge[ee];

        	                auxInt = abs(ii - jj);
        	                if (auxInt > halfNodes) auxInt = nNodes - auxInt;
        	                if (auxInt <= K) edgeLD[ee] = 1;
        	                else edgeLD[ee] = 0;
        	        }
        	}

		//-------- Vaccination --------//
		
		if (flagActVacc)
		{
        		for (nn=0; nn<nNodes; nn++) vaccTime[nn] = 15;

        		// Vaccination order by node degree or randomly
        		for (ii=0; ii<nNodes; ii++) vaccOrder[ii] = ii;
        		if (flagOrderDegree)
        		        quickSort(vaccOrder, nodeDegree, nNodes);
        		else
        		{
        		        // Shuffles the indexes of the nodes (random order)
        		        for (ii=0; ii<nNodes; ii++)
        		        {
        		                jj = ranUni.int32()%(ii+1);
        		                if (jj == ii) continue;
        		                swap(vaccOrder[ii],vaccOrder[jj]);
        		        }
        		}
        		// Initial vaccinated nodes (10 -> recently vaccinated)
        		if (flagInitVacc)
			{
				for (ii=0; ii<vaccGoal; ii++) nodeStatus[vaccOrder[ii]] = 10;
				flagActVacc = 0;
			}
		}


	}
	
	//===| GENERATES THE NETWORK |===//
	


	if (netModel == 0) // Wattz-Strogatz network (ER -> beataWS = 1.0)
		genWSnet(edge, nodeDegree, nEdges, nNodes, K, betaWS, ranUni);

	if (netModel == 1) // Barabasi-Albert network
		genBAnet(edge, nodeDegree, nNodes, K, ranUni);

	// Lockdown:

        if (flagActLD) for (ee=0; ee<nEdges; ee++)
        {
                if (probRandomLD > 0.0)
                        if (ranUni.doub() > probRandomLD) edgeLD[ee] = 1;
                        else edgeLD[ee] = 0;
                else
                {
                        ii = ee/K;
                        jj = edge[ee];

                        auxInt = abs(ii - jj);
                        if (auxInt > halfNodes) auxInt = nNodes - auxInt;
                        if (auxInt <= K) edgeLD[ee] = 1;
                        else edgeLD[ee] = 0;
                }
        }

	//===| SIMULATION |===//
	
	FILE *fNetStatus;
	fNetStatus = fopen("netStatus.dat", "w");
	fprintf(fNetStatus, "#Day\tS\tE\tA\tI\tR\tE2\tA2\tI2\tR2\n");

	FILE *fNewCases;
	fNewCases = fopen("newCases.dat", "w");
	fprintf(fNewCases, "#Day\tE\tA\tI\tR\tE2\tA2\tI2\tR2\tLock\n");

	// Status (SEAIR: Susceptible, Exposed, Asymptomatic, Infected, Removed)
	// 0:S, 1:E1, 2:A1, 3:I1, 4:R1, -1:E2, -2:A2, -3:I2, -4:R2 
	short *nodeStatus, *nodeInfec;	

	nodeStatus = (short*) malloc(nNodes*sizeof(short));
	memset(nodeStatus, 0, nNodes*sizeof(short)); // All nodes are susceptibles
	nodeInfec = (short*) malloc(nNodes*sizeof(short));
	memset(nodeInfec, 0, nNodes*sizeof(short));

	int nn;
	int *expTimeNode, *infecTimeNode;

	expTimeNode = (int*) malloc(nNodes*sizeof(int));
	for (nn=0; nn<nNodes; nn++) expTimeNode[nn] = gammaE.dev();
	infecTimeNode = (int*) malloc(nNodes*sizeof(int));
	for (nn=0; nn<nNodes; nn++) infecTimeNode[nn] = gammaI.dev();

	int nContagious;
	int nSuscep, nExpo, nAsymp, nInfec, nRem;
	int nExpo2, nAsymp2, nInfec2, nRem2;
	int newE, newA, newI, newR, newE2, newA2, newI2, newR2, oldI, daysNewI;
	short iiStatus, jjStatus;

	nSuscep = nNodes;
	nExpo = 0;
	nAsymp = 0;
	nInfec = 0;
	nRem = 0;
	nExpo2 = 0;
	nAsymp2 = 0;
	nInfec2 = 0;
	nRem2 = 0;

	newE = 0;
	newA = 0;
	newI = 0;
	newR = 0;
	newE2 = 0;
	newA2 = 0;
	newI2 = 0;
	newR2 = 0;
	oldI = 0;
	daysNewI = 0;

	// Choosing random node for Infected status
	for (nn=0; nn<initInfec; nn++)
	{
		auxInt = ranUni.int32()%nNodes;
		while (nodeStatus[auxInt] != 0) auxInt = ranUni.int32()%nNodes;
		nodeStatus[auxInt] = 2; // Infected
		nSuscep--;
		nInfec++;
		newI++;
	}

	short flagVacc;
	short *vaccTime, *vaccStatus;
	int *vaccOrder;
	int vaccGoal, vaccPerDay, idxV;
	float ineff1, ineff2;

	vaccTime = (short*) malloc(nNodes*sizeof(short));
	for (nn=0; nn<nNodes; nn++) vaccTime[nn] = 14;
	vaccStatus = (short*) malloc(nNodes*sizeof(short));
	memset(vaccStatus, 0, nNodes*sizeof(short));

	// Vaccination order
	vaccOrder = (int*) malloc(nNodes*sizeof(int));
	for (ii=0; ii<nNodes; ii++) vaccOrder[ii] = ii;

	// Order by node degree
	if (flagOrderDegree)
		quickSort(vaccOrder, nodeDegree, nNodes);
	else
	{
		// Shuffles the indexes of the nodes (random order)
		for (ii=0; ii<nNodes; ii++)
		{
			jj = ranUni.int32()%(ii+1);
			if (jj == ii) continue;
			swap(vaccOrder[ii],vaccOrder[jj]);
		}
	}

	idxV = 0;
	flagVacc = 0;
	ineff1 = 0.35;
	ineff2 = 0.05;
	vaccGoal = vaccFrac*nNodes;
	vaccPerDay = vaccPerDayFrac*vaccGoal;

	// Initial vaccinated nodes
	//for (ii=0; ii<vaccGoal; ii++) vaccStatus[vaccOrder[ii]] = 1;

	short flagLockdown, flagVariant2, switchLD, count, countV;
	int time, timeLD;
	float auxF;

	flagVariant2 = 0;
	flagLockdown = 0;
	switchLD = 0;
	count = 0;
	countV = 0;
	time = 0;
	timeLD = 0;
	int sumI = 0;
        int sumI2 = 0;

	while (1)
	{

		nContagious = nExpo + nAsymp + nInfec + nExpo2 + nAsymp2 + nInfec2;

		// Print the network status
		fprintf(fNetStatus, "%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\n",
				time, nSuscep, nExpo, nAsymp, nInfec, nRem,
				nExpo2, nAsymp2, nInfec2, nRem2);
		
		// Print new cases
		fprintf(fNewCases, "%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\n",
				time, newE, newA, newI, newR, newE2, newA2, newI2, newR2, flagVacc);
		sumI += newI;
                sumI2 += newI2;

		time++;

		if (flagActLD) if (!flagLockdown)
                {
                        if (newI + newI2 > oldI) daysNewI++;
                        else daysNewI = 0;
                        oldI = newI + newI2;
                        if (daysNewI > ldStart)
			{
				flagLockdown = 1; // Activate lockdown once
                                switchLD = 1;
			}
		}

                if (flagLockdown == 1)
                {
                	if (interval > 0)
                	{
                        	count++;
                        	if (count > interval)
                        	{
                                       	count = 0;
                                       	if (switchLD) switchLD = 0;
               	                	else switchLD = 1;
                        	}
                        }

                        timeLD++;
                       	if (timeLD > ldEnd)
                        {
                        	flagLockdown = 2;
                        	switchLD = 0;
                        }
                }

		if (flagActVacc) if (!flagVacc)
                {
                        if (newI + newI2 > oldI) daysNewI++;
                        else daysNewI = 0;
                        oldI = newI + newI2;
                        if (daysNewI > vaccStart)
			{
                        	flagVacc = 1; // Activate vaccination
				if (vaccPerDay == 0) flagVacc = 3; // Deactivate vaccination
			}
		}

		if (flagVacc == 1)
		{
			countV++;
			if (countV == 7) flagVacc = 2;
		}

		newE = 0;
		newI = 0;
		newR = 0;
		newE2 = 0;
		newI2 = 0;
		newR2 = 0;

		if (nContagious == 0)
                {
                        if (variant2Intro == 0.0) break;
                        if (flagVariant2 == 1) break;
                        if (time < variant2Intro) continue;
                }


		if (time > maxDays) break;

		// Vaccinates Susceptible nodes
                if (flagVacc == 2)
                {
                        nn = 0;
                        while (nn<vaccPerDay)
                        {
                                if (idxV == nNodes) break;
                                auxInt = vaccOrder[idxV];
                                idxV++;
                                if (nodeStatus[auxInt] != 0) continue;
                                if (vaccStatus[auxInt] != 0) continue;
                                vaccStatus[auxInt] = 1;
                                nn++;
                                vaccGoal--;
                                if (vaccGoal == 0) break;
                        }
                        if (vaccGoal == 0) flagVacc = 3;
                        if (idxV == nNodes) flagVacc = 3;
                }

                // Finds a Susceptible (0) node and infects it with variant 2
                if (time == variant2Intro)
                {
                        flagVariant2 = 1;
                        for (nn=0; nn<initInfec; nn++)
                        {
                                auxInt = ranUni.int32()%nNodes;
                                while (nodeStatus[auxInt] != 0) auxInt = ranUni.int32()%nNodes;
                                nodeStatus[auxInt] = -2; // Infected -2
                                //nodeStatus[auxInt] = -1; // Exposed -1
                                nSuscep--;
                                nInfec2++;
                                newI2++;
                        }
                }

		// Identifies the suceptible nodes and determine if they will be infected
		for (ee=0; ee<nEdges; ee++)
		{
			// Lockdown resriction
                        if (switchLD) if(edgeLD[ee] == 0) continue;

			ii = ee/K;
			jj = edge[ee];

			iiStatus = nodeStatus[ii];
			jjStatus = nodeStatus[jj];

			if (iiStatus == 0) // Susceptible
			{
				auxInt = vaccStatus[ii];
				if (auxInt == 0) auxF = 1.0; // No vaccinated
				if (auxInt == 1) auxF = ineff1; // Vaccinated with one dose 
				if (auxInt == 2) auxF = ineff2; // Vaccinated with two doses 

				//if (jjStatus == 1) if (ranUni.doub() <= auxF*probInfec1)
				if (jjStatus == 2 || jjStatus == 1) if (ranUni.doub() <= auxF*probInfec1)
				{
					nodeInfec[ii] = 1;
					if (auxInt == 1) vaccStatus[ii] = -1;
					if (auxInt == 2) vaccStatus[ii] = -2;
				}
				//if (jjStatus == -1) if (ranUni.doub() <= probInfec2) nodeInfec[ii] = -1;
				if (jjStatus == -2 || jjStatus == -1) if (ranUni.doub() <= probInfec2) nodeInfec[ii] = -1;
			}

			if (iiStatus == 3) // Removed 1
                        {
                                //if (jjStatus == -1) if (ranUni.doub() <= probInfec2) nodeInfec[ii] = -1;
                                if (jjStatus == -2 || jjStatus == -1) if (ranUni.doub() <= probInfec2) nodeInfec[ii] = -1;
                        }

			if (jjStatus == 0) // Susceptible
			{
				auxInt = vaccStatus[jj];
				if (auxInt == 0) auxF = 1.0; // No vaccinated
				if (auxInt == 1) auxF = ineff1; // Vaccinated with one dose 
				if (auxInt == 2) auxF = ineff2; // Vaccinated with two doses 

				//if (iiStatus == 1) if (ranUni.doub() <= auxF*probInfec1)
				if (iiStatus == 2 || iiStatus == 1) if (ranUni.doub() <= auxF*probInfec1)
				{
					nodeInfec[jj] = 1;
					if (auxInt == 1) vaccStatus[jj] = -1;
					if (auxInt == 2) vaccStatus[jj] = -2;
				}
				//if (iiStatus == -1) if (ranUni.doub() <= probInfec2) nodeInfec[jj] = -1;
				if (iiStatus == -2 || iiStatus == -1) if (ranUni.doub() <= probInfec2) nodeInfec[jj] = -1;
			}

			if (jjStatus == 3) // Removed 1
                        {
                                //if (iiStatus == -2 || iiStatus == -1) if (ranUni.doub() <= probInfec2) nodeInfec[jj] = -1;
                                if (iiStatus == -1) if (ranUni.doub() <= probInfec2) nodeInfec[jj] = -1;
                        }

		}

		// Update states
		for (ii=0; ii<nNodes; ii++)
		{
			// Update status of the vaccination
			if (vaccStatus[ii] == 1)
			{
				vaccTime[ii]--;
				if (vaccTime[ii] == 0) vaccStatus[ii] = 2; // booster
			}

			iiStatus = nodeStatus[ii];

			if (iiStatus == 0) // Suceptible
			{
				if (nodeInfec[ii] == 1)
				{
					nodeStatus[ii] = 1;
					nSuscep--;
					nExpo++;
					newE++;
				}

				if (nodeInfec[ii] == -1)
				{
					nodeStatus[ii] = -1;
					nSuscep--;
					nExpo2++;
					newE2++;
				}
				nodeInfec[ii] = 0;
				continue;
			}

			if (iiStatus == 1) // Exposed 1
			{
				expTimeNode[ii]--;
				if (expTimeNode[ii] > 0) continue;
				if (ranUni.doub() <= probDevInfec)
				{
					nodeStatus[ii] = 2; // Infected
					nExpo--;
					nInfec++;
					newI++;
				}
				else
				{
					nodeStatus[ii] = 3; // Removed
					nExpo--;
					nRem++;
					newR++;
				}
				expTimeNode[ii] = gammaE.dev();
				continue;
			}

			if (iiStatus == -1) // Exposed 2
			{
				expTimeNode[ii]--;
				if (expTimeNode[ii] > 0) continue;
				if (ranUni.doub() <= probDevInfec)
				{
					nodeStatus[ii] = -2; // Infected 2
					nExpo2--;
					nInfec2++;
					newI2++;
				}
				else
				{
					nodeStatus[ii] = -3; // Removed 2
					nExpo2--;
					nRem2++;
					newR2++;
				}
				continue;
			}

			if (iiStatus == 2) // Infected 1
			{
				infecTimeNode[ii]--;
				if (infecTimeNode[ii] > 0) continue;
				nodeStatus[ii] = 3; // Removed
				nInfec--;
				nRem++;
				newR++;
				infecTimeNode[ii] = gammaI.dev();
				continue;
			}

			if (iiStatus == -2) // Infected 2
			{
				infecTimeNode[ii]--;
				if (infecTimeNode[ii] > 0) continue;
				nodeStatus[ii] = -3; // Removed 2
				nInfec2--;
				nRem2++;
				newR2++;
				continue;
			}

			if (iiStatus == 3) // Removed 1
                        {
                                if (nodeInfec[ii] == -1)
                                {
                                        nodeStatus[ii] = -1;
                                        nRem--;
                                        nExpo2++;
                                        newE2++;
                                }
                                nodeInfec[ii] = 0;
                                continue;
                        }

		}
	}

	fclose(fNetStatus);
	fclose(fNewCases);

	FILE *fVacc;
        fVacc = fopen("vaccSummary.dat", "w");
        fprintf(fVacc, "#Goal?\tfullVacc\tinfecD1\tinfecD2\n");
        int noVacc, vaccD2, infecD1, infecD2;
        noVacc = 0;
        vaccD2 = 0;
        infecD1 = 0;
        infecD2 = 0;
        for (nn=0; nn<nNodes; nn++)
        {
                auxInt = vaccStatus[nn];
                if (auxInt == 0) noVacc++;
                if (auxInt == 2) vaccD2++;
                if (auxInt == -1) infecD1++;
                if (auxInt == -2) infecD2++;
        }
        vaccGoal = vaccFrac*nNodes;
        if (vaccGoal > nNodes - noVacc) fprintf(fVacc, "0\t");
        else fprintf(fVacc, "1\t");
        fprintf(fVacc, "%d\t%d\t%d\n", vaccD2, infecD1, infecD2);
        fclose(fVacc);

	FILE *fSum;
        fSum = fopen("totalInfec.dat", "w");
        fprintf(fSum, "#Tot\tTot_I1\tTot_I2\n");
        fprintf(fSum, "%d\t%d\t%d\n", sumI+sumI2, sumI, sumI2);
        fclose(fSum);


	free(nodeStatus);
	free(nodeInfec);
	free(expTimeNode);
	free(infecTimeNode);
	free(vaccStatus);
	free(vaccTime);
	free(vaccOrder);
	free(edge);
	free(edgeLD);

	exit (0);
}
