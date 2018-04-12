/*
 * ns3 simulation:
 * Performance evaluation of IEEE 802.11b WiFi network in adhoc mode.
 * Friis path loss is considered.
 * Traffic is sent at a Constant Bit Rate (CBR)
 * Mobility: Random Waypoint Mobility Model
 *
 * Author: Leonardo Bonati
 * Date: Dec. 2017
 *
 */

#include "ns3/applications-module.h"
#include "ns3/config-store-module.h"
#include "ns3/core-module.h"
#include "ns3/csma-module.h"
#include "ns3/energy-module.h"
#include "ns3/flow-monitor-module.h"
#include "ns3/internet-module.h"
#include "ns3/ipv4-list-routing-helper.h"
#include "ns3/ipv4-static-routing-helper.h"
#include "ns3/mobility-module.h"
#include "ns3/network-module.h"
#include "ns3/olsr-helper.h"
#include "ns3/point-to-point-module.h"
#include "ns3/propagation-module.h"
#include "ns3/trace-helper.h"
#include "ns3/wifi-module.h"

#include <fstream>
#include <iostream>
#include <string>
#include <vector>
#include <map>
#include <ctime>
#include <cstdlib>
#include <cmath>

using namespace std;
using namespace ns3;

uint32_t sink_tx_pkts = 0;
uint32_t sink_rx_pkts = 0;
uint32_t sink_rx_udp = 0;
uint32_t source_tx_pkts = 0;
uint32_t source_rx_pkts = 0;
uint32_t source_tx_udp = 0;
uint32_t all_pkts = 0;

uint32_t nodes_number = 50;
uint32_t sink_id = 0;                       // id number of sink node

double area_size = 100;
double min_path_loss = 0.;                  // minimum path loss [dB]

std::string base_name = "adhoc-res_" + std::to_string(static_cast<int>(area_size)) + "_" + std::to_string(nodes_number) + "_" + std::to_string(static_cast<int>(min_path_loss));      // base name
std::string file_name = base_name + ".txt";
std::string trace_name = base_name + ".tr";

uint32_t simulations_number = 33;           // number of simulations to run

double rx_power_wc = 1.;                    // set desired received power in the worst case [W]

double antenna_gain_tx = 16;                // transmitting antenna gain [dB]
double antenna_gain_rx = 44;                // receiving antenna gain [dB]
double lambda = 0.125;                      // wavelength [m] --> c/f, with f=2.4GHz used by IEEE802.11b

// further possible distance of client [m]
double dist_wc = sqrt(2. * pow(area_size/2., 2));

// worst case path loss
double Pl_wc = 1.0 / (pow(10, antenna_gain_tx/10.) * pow(10, antenna_gain_rx/10.)) * pow((4. * 3.14 * dist_wc)/lambda, 2);

// transmitter power [dBm]
double tx_power = 10*log10(rx_power_wc * Pl_wc * pow(10, 3));

// UDP parameters
uint32_t packet_size = 597;                 // bytes --> 597 bytes + 28 bytes header
uint32_t numPackets = 20000;
uint32_t max_bytes = numPackets * packet_size;
double interval = 0.005;                    // inter packet interval [s]

std::string phyMode("DsssRate1Mbps");       // set constant rate for both control and data

uint32_t mac_addr_len = 17;                 // length of mac address string

bool verbose = false;
bool use_udp_server = false;                // true -> install UPD server on sink, false -> install PacketSink application on sink
bool start_clients_diff_times = false;
bool show_sim_number = true;

std::string udp_header_format = "UdpHeader";
std::string sink_mac = "";

map<string, uint32_t> sink_rx_mac_cbr;          // maps mac_addr with number of data packets received by sink
map<string, uint32_t> sink_rx_mac_ctl;          // maps mac_addr with number of control packets received by sink

map<string, string> ip_mac_map;                 // maps IP addresses and MAC addresses
map<string, uint32_t> ip_id_map;                // maps IP addresses and node IDs

map<string, double> mac_throughput_map;         // maps source mac address with throughput

uint32_t pkt_no = 0;
double sum_thr = 0;


// get node MAC address from IP address
std::string get_mac_from_ip(std::string ip_addr){
    
    std::map<std::string, std::string>::iterator iter = ip_mac_map.find(ip_addr);
    return iter->second;
}

// increase integer counter related to a specific MAC address, or add MAC address to map
void add_to_map(std::string dst_mac, map<string, uint32_t> *mp){
    
    std::map<std::string, uint32_t>::iterator iter = mp->find(dst_mac);
    
    if (iter != mp->end()){                 // element is present -> increment value of counter
        uint32_t tmp = mp->at(dst_mac);
        iter->second = tmp + 1;
    }
    else {                                  // element is not present -> add it
        mp->insert(std::pair<std::string, uint32_t>(dst_mac, 1));
    }
}

// add pair <MAC, double value> to map
void add_value_to_map(std::string mac_addr, map<string, double> *mp, double value){
    
    std::map<std::string, double>::iterator iter = mp->find(mac_addr);
    
    if (iter != mp->end()){                 // element is present -> increment value of counter
        uint32_t tmp = mp->at(mac_addr);
        iter->second = tmp + value;
    }
    else {                                  // element is not present -> add it
        mp->insert(std::pair<std::string, double>(mac_addr, value));
    }
}

// get packet destination MAC address
std::string get_pkt_dest_mac(const Ptr<const Packet> p){
    
    std::string dst_mac = "";
    
    std::string pkt = p->ToString();
    
    // packet is data
    if (pkt.find("DATA") != std::string::npos){
        
        // save mac destination address
        dst_mac = pkt.substr(pkt.find("DA=") + 3, mac_addr_len);
    }
    else if (pkt.find("CTL_ACK") != std::string::npos){
        
        dst_mac = pkt.substr(pkt.find("RA=") + 3, mac_addr_len);
    }
    else {
        std::cout << "\t[ERR] Address not found: " << pkt << "\n";
    }
    
    return dst_mac;
}

// get packet source MAC address
std::string get_pkt_src_mac(const Ptr<const Packet> p){
    
    std::string src_mac = "";
    
    std::string pkt = p->ToString();
    
    // packet is data
    if (pkt.find("DATA") != std::string::npos){
        
        // save mac source address
        src_mac = pkt.substr(pkt.find("SA=") + 3, mac_addr_len);
    }
    else if (pkt.find("CTL_ACK") != std::string::npos){
        
        src_mac = pkt.substr(pkt.find("RA=") + 3, mac_addr_len);
    }
    else {
        std::cout << "\t[ERR] Address not found: " << pkt << "\n";
    }
    
    return src_mac;
}

// increase counter when sink transmits a packet
void sink_tx(std::string context, const Ptr<const Packet> p){
    
    if (verbose) {
        std::cout << Simulator::Now().GetSeconds() << "\t[SNK] Packet Transmitted\n";
    }
    
    sink_tx_pkts++;
    
}

// increase counter when sink receives a packet
void sink_rx(std::string context, const Ptr<const Packet> p){
    
    if (verbose) {
        std::cout << Simulator::Now().GetSeconds() << "\t[SNK] Packet Received\n";
    }
    
    // look for UDP packet
    std::string pkt = p->ToString();
    
    // find source address
    std::string src_mac = get_pkt_src_mac(p);
    
    // packet is present
    if (pkt.find(udp_header_format) != std::string::npos){
        sink_rx_udp++;
        
        std::map<std::string, uint32_t> *map = &sink_rx_mac_cbr;
        add_to_map(src_mac, map);
    }
    else {                                                              // packet is control
        
        std::map<std::string, uint32_t> *map = &sink_rx_mac_ctl;
        
        // add twice: one for broadcast msg and one for ctl_ack (two contro packets associated)
        add_to_map(src_mac, map);
        add_to_map(src_mac, map);
    }
    
    sink_rx_pkts++;
}

// increase counter when source transmits a packet
void source_tx(std::string context, const Ptr<const Packet> p){
    
    if (verbose){
        std::cout << Simulator::Now().GetSeconds() << "\t[SRC] Packet Transmitted\n";
    }
    
    // look for UDP packet
    std::string pkt = p->ToString();
    std::string udp_header_format = "UdpHeader";
    
    // packet is present
    if (pkt.find(udp_header_format) != std::string::npos) {
        source_tx_udp++;
    }
    
    source_tx_pkts++;
    all_pkts++;
}

// increase counter when source receives a packet
void source_rx(std::string context, const Ptr<const Packet> p){
    
    if (verbose) {
        std::cout << Simulator::Now().GetSeconds() << "\t[SRC] Packet Received\n";
    }
    
    source_rx_pkts++;
    all_pkts++;
    
}

// generate random double number in [f_min, f_max]
double random_number(double f_min, double f_max){
    
    double f = (double)rand() / RAND_MAX;
    return f_min + f * (f_max - f_min);
}


int main (int argc, char **argv){
    
    // open output file
    ofstream myfile;
    myfile.open (file_name);
    
    std::ostringstream initial_stream;
    
    // print simulation info
    initial_stream << "------------------simulation info--------------------\n";
    initial_stream << "\nNumber of nodes:\t" << nodes_number << "\n";
    initial_stream << "Area size:\t\t" << area_size << " sqm\n";
    initial_stream << "Transmitting power:\t" << tx_power << " dBm\n";
    initial_stream << "Sources antenna gain:\t" << antenna_gain_tx << " dB\n";
    initial_stream << "Sink antenna gain:\t" << antenna_gain_rx << " dB\n";
    
    initial_stream << "Minimum path loss:\t" << min_path_loss << " dB\n";
    if (min_path_loss < 10*log10(Pl_wc)){
        initial_stream << "Worst case path loss:\t" << 10*log10(Pl_wc) << " dB\n";
        initial_stream << "Worst case RX power:\t" << 10*log10(rx_power_wc * pow(10, 3)) << " dBm\n";
    }
    else {
        initial_stream << "\n\tMinimum path loss higher than worst case path loss\n\n";
        initial_stream << "Worst case RX power:\t" << tx_power - min_path_loss - 30. << " dBm\n\n";
    }
    
    initial_stream << "Number of simulations:\t" << simulations_number << "\n\n";
    
    // print initial stream both on file and on standard output
    std::cout << "\n" << initial_stream.str();
    myfile << initial_stream.str();
    
    // initialize random number generator with different seed
    srand(time(0));
    double lowest = 0.;
    double highest = 120.;
    
    // create vectors to store inter-simulation results
    vector <double> thr_vec(nodes_number-1);
    vector <uint32_t> sink_rx_data_vec(nodes_number-1);
    vector <uint32_t> sink_rx_tot_vec(nodes_number-1);
    
    // initialize vectors
    for (uint32_t i=0; i<nodes_number-1; i++){
        thr_vec[i]=0.;
        sink_rx_data_vec[i]=0;
        sink_rx_tot_vec[i]=0;
    }
    
    // run different simulations
    for (uint32_t sim = 0; sim < simulations_number; sim++){
        
        if (show_sim_number){
            std::cout << "Simulation " << sim+1 << " of " << simulations_number << "\n";
        }
        
        CommandLine cmd;
        cmd.Parse(argc, argv);
        
        // erase maps
        sink_rx_mac_cbr.clear();
        sink_rx_mac_ctl.clear();
        
        ip_mac_map.clear();
        ip_id_map.clear();
        
        // create nodes
        NodeContainer nodes;
        nodes.Create(nodes_number);
        
        // setup sink mobility model
        // create uniform rv
        Ptr<UniformRandomVariable> uni = CreateObject<UniformRandomVariable> ();
        uni->SetAttribute ("Min", DoubleValue (0.));
        uni->SetAttribute ("Max", DoubleValue (area_size));
        
        // set fixed position for AP
        MobilityHelper fixedMobility;
        
        //fix position for access point
        Ptr<ListPositionAllocator> fixedAlloc = CreateObject <ListPositionAllocator>();
        fixedAlloc ->Add(Vector(area_size / 2., area_size / 2., 0));      //AP position
        
        // assign fixed mobility model to sink
        fixedMobility.SetPositionAllocator(fixedAlloc);
        fixedMobility.SetMobilityModel("ns3::ConstantPositionMobilityModel");
        fixedMobility.Install(nodes.Get(sink_id));
        
        // setup wifi
        WifiHelper wifi;
        wifi.SetStandard (WIFI_PHY_STANDARD_80211b);
        
        // install wireless devices
        YansWifiPhyHelper wifiPhy =  YansWifiPhyHelper::Default ();
        
        // setup powers and gains
        wifiPhy.Set("TxGain", DoubleValue(antenna_gain_tx));
        wifiPhy.Set("RxGain", DoubleValue(antenna_gain_rx));
        wifiPhy.Set("TxPowerStart",DoubleValue(tx_power));
        wifiPhy.Set("TxPowerEnd",DoubleValue(tx_power));
        wifiPhy.Set("Frequency",UintegerValue(2400));
        
        // ns-3 supports RadioTap and Prism tracing extensions for 802.11b
        wifiPhy.SetPcapDataLinkType(YansWifiPhyHelper::DLT_IEEE802_11_RADIO);
        
        // setup propagation model and minimum path loss
        YansWifiChannelHelper wifiChannel = YansWifiChannelHelper::Default ();
        wifiChannel.SetPropagationDelay ("ns3::ConstantSpeedPropagationDelayModel");
        wifiChannel.AddPropagationLoss ("ns3::FriisPropagationLossModel", "MinLoss", DoubleValue(min_path_loss), "Frequency", DoubleValue(2.4e09));
        wifiPhy.SetChannel (wifiChannel.Create ());
        
        // Add a non-QoS upper mac, and disable rate control
        NqosWifiMacHelper wifiMac = NqosWifiMacHelper::Default();
        wifi.SetRemoteStationManager("ns3::ConstantRateWifiManager",
                                     "DataMode", StringValue(phyMode),
                                     "ControlMode", StringValue(phyMode));
        
        // use ad-hoc MAC
        wifiMac.SetType ("ns3::AdhocWifiMac");
        NetDeviceContainer devices = wifi.Install (wifiPhy, wifiMac, nodes);
        
        // install internet
        InternetStackHelper internet;
        internet.Install (nodes);
        
        // install IPv4
        Ipv4AddressHelper ipv4;
        ipv4.SetBase ("10.1.1.0", "255.255.255.0");
        Ipv4InterfaceContainer interfaces = ipv4.Assign (devices);
        
        // map IPv4 addresses and MAC addresses and to node_id
        for (uint32_t i=0; i<nodes_number; i++){
            
            // get node MAC address
            std::ostringstream tmp_mac;
            tmp_mac << nodes.Get(i)->GetDevice(0)->GetAddress();
            
            // get node IP address
            std::ostringstream tmp_ip;
            Ptr<Ipv4> tmp_ipv4 = nodes.Get(i)->GetObject<Ipv4>();
            Ipv4InterfaceAddress iaddr = tmp_ipv4->GetAddress (1,0);
            Ipv4Address addri = iaddr.GetLocal ();
            tmp_ip << addri;
            
            ip_mac_map.insert(std::pair<std::string, std::string>(tmp_ip.str(), tmp_mac.str().substr(6, mac_addr_len)));
            ip_id_map.insert(std::pair<std::string, uint32_t>(tmp_ip.str(), i));
            
            // save sink MAC address
            if (i == sink_id){
                sink_mac = tmp_mac.str().substr(6, mac_addr_len);
            }
        }
        
        // setuo position allocator that will be used by the RandomWaypoint Mobility Model
        RandomRectanglePositionAllocator posAllocator;
        MobilityHelper mobility;
        
        // assign Random Waypoint mobility model to source nodes
        for (uint32_t i=0; i<nodes_number; i++){
            
            if (i != sink_id){
                
                posAllocator.SetX(uni);
                posAllocator.SetY(uni);
                
                mobility.SetMobilityModel ("ns3::RandomWaypointMobilityModel",
                                           "Speed", StringValue ("ns3::UniformRandomVariable[Min=1.0|Max=12.0]"),
                                           "PositionAllocator", PointerValue(&posAllocator));
                mobility.Install(nodes.Get(i));
            }
        }
        
        
        // setup sink
        uint32_t port = 4000;
        ApplicationContainer sink_app;
        
        if (use_udp_server){            // use UDP server
            // install UDP server application on sink
            UdpServerHelper server(port);
            sink_app = server.Install(nodes.Get(sink_id));
        }
        else {                          // use UDP sink
            // install PacketSink application on sink
            PacketSinkHelper sink ("ns3::UdpSocketFactory", Address (InetSocketAddress (interfaces.GetAddress(sink_id), port)));
            sink_app = sink.Install (nodes.Get(sink_id));
        }
        
        sink_app.Start(Seconds(1.));
        sink_app.Stop(Seconds(150.));
        
        // setup UDP client
        UdpClientHelper client(interfaces.GetAddress(sink_id), port);
        client.SetAttribute("MaxPackets", UintegerValue(numPackets));
        client.SetAttribute("Interval", TimeValue(Seconds(interval)));
        client.SetAttribute("PacketSize", UintegerValue(packet_size));
        
        // install client on nodes
        for (uint32_t i = 0; i < nodes_number; i++){
            
            if (i != sink_id){
                
                double rn;
                ApplicationContainer clientApps = client.Install(nodes.Get(i));
                
                if (start_clients_diff_times){              // start client at different times
                    rn = random_number(lowest, highest);
                    clientApps.Start(Seconds(2. + rn));
                }
                else {                                      // start client at almost the same time
                    rn = random_number(0., 1.);
                    clientApps.Start(Seconds(2. + rn));
                }
                
                clientApps.Stop(Seconds(149.));
            }
        }
        
        // enable traces
        bool tracing = true;
        bool asciiTracing = true;
        
        if (tracing) {
            if (asciiTracing) {
                AsciiTraceHelper ascii;
                wifiPhy.EnableAsciiAll(ascii.CreateFileStream(trace_name));
            }
        }
        
        // setup callbacks to trace packet events
        std::ostringstream sink_path_tx;
        sink_path_tx << "/NodeList/" << sink_id << "/DeviceList/0/$ns3::WifiNetDevice/Phy/PhyTxBegin";
        Config::Connect(sink_path_tx.str(), MakeCallback(&sink_tx));
        
        std::ostringstream sink_path_rx;
        sink_path_rx << "/NodeList/" << sink_id << "/DeviceList/0/$ns3::WifiNetDevice/Phy/PhyRxEnd";
        Config::Connect(sink_path_rx.str(), MakeCallback(&sink_rx));
        
        
        // assign the trace to nodes
        for (uint32_t iter = 0; iter < nodes_number; ++iter) {
            
            if (iter != sink_id) {
                
                std::ostringstream source_path_tx;
                source_path_tx << "/NodeList/" << iter << "/DeviceList/0/$ns3::WifiNetDevice/Phy/PhyTxBegin";
                Config::Connect(source_path_tx.str(), MakeCallback(&source_tx));
            }
        }
        
        for (uint32_t iter = 0; iter < nodes_number; ++iter) {
            
            if (iter != sink_id) {
                
                std::ostringstream source_path_rx;
                source_path_rx << "/NodeList/" << iter << "/DeviceList/0/$ns3::WifiNetDevice/Phy/PhyRxEnd";
                Config::Connect(source_path_rx.str(), MakeCallback(&source_rx));
            }
        }
        
        // install FlowMonitor
        FlowMonitorHelper flowmon;
        Ptr<FlowMonitor> monitor = flowmon.InstallAll ();
        
        // run simulation
        Simulator::Stop (Seconds (150));
        Simulator::Run ();
        
        // flow statistics
        monitor->CheckForLostPackets();
        Ptr<Ipv4FlowClassifier> classifier = DynamicCast<Ipv4FlowClassifier>(flowmon.GetClassifier());
        std::map<FlowId, FlowMonitor::FlowStats> stats = monitor->GetFlowStats();
        
        uint32_t flow_no = -1;
        for (std::map<FlowId, FlowMonitor::FlowStats>::const_iterator iters = stats.begin(); iters != stats.end(); ++iters) {
            
            flow_no++;
            Ipv4FlowClassifier::FiveTuple t = classifier->FindFlow(iters->first);
            
            // get source IP and MAC addresses
            std::ostringstream tx_ip_tmp;
            tx_ip_tmp << t.sourceAddress;
            std::string tx_ip = tx_ip_tmp.str();
            std::string tx_mac = get_mac_from_ip(tx_ip);
            
            // get flow throughput
            std::ostringstream thr_tmp;
            thr_tmp << iters->second.rxBytes * 8. / (iters->second.timeLastRxPacket.GetSeconds() - iters->second.timeFirstTxPacket.GetSeconds()) / 1024.;
            std::string thr_str = thr_tmp.str();
            double thr_d = std::stod(thr_str);
            
            if (!isnan(thr_d)){
                thr_vec[flow_no]+=thr_d;
            }

            // get received number of CBR packets
            std::map<std::string, uint32_t>::iterator iter;
            iter = sink_rx_mac_cbr.find(tx_mac);
            uint32_t cbr_rx_sink = iter->second;

            // store value
            if (!isnan(cbr_rx_sink)){
                sink_rx_data_vec[flow_no]+=cbr_rx_sink;
            }

            // get total number of received packets
            iter = sink_rx_mac_ctl.find(tx_mac);
            uint32_t ctl_rx_sink = iter->second;
            uint32_t total_rx_sink = cbr_rx_sink + ctl_rx_sink;

            if (!isnan(total_rx_sink)){
                sink_rx_tot_vec[flow_no]+=total_rx_sink;
            }
            
            // increase counters
            pkt_no = pkt_no + iters->second.txPackets;
            sum_thr = sum_thr + iters->second.rxBytes * 8. / (iters->second.timeLastRxPacket.GetSeconds() - iters->second.timeFirstTxPacket.GetSeconds()) / 1024.;
            
            
            // print statistics if last simulation round
            if (sim == simulations_number - 1){

                // print average flow statistics
                if (iters->first == 1){
                    myfile << "------------end source-destination pairs-------------\n\n";
                }

                myfile << "Flow ID: " << iters->first << " Src Addr " << t.sourceAddress << " Dst Addr " << t.destinationAddress << "\n";

                // get average flow throughput
                double avg_flow_thr = thr_vec[flow_no];
                avg_flow_thr = avg_flow_thr * 1. / ((simulations_number+nodes_number-1) / (nodes_number-1));
                myfile << "Average flow throughput:\t\t" << avg_flow_thr << " kbps\n";

                // get received number of CBR packets
                double cbr_rx_sink = sink_rx_data_vec[flow_no];
                cbr_rx_sink = cbr_rx_sink * 1. / simulations_number;
                myfile << "Number of received CBR:\t\t\t" << cbr_rx_sink << "\n";

                // get total number of received packets
                double tot_rx_sink = sink_rx_tot_vec[flow_no];
                tot_rx_sink = tot_rx_sink * 1. / simulations_number;
                myfile << "Total number of received packets:\t" << tot_rx_sink << "\n";

                // compute PCBR
                double pcbr = cbr_rx_sink * 1. / tot_rx_sink * 100.;
                myfile << "PCBR:\t\t\t\t\t" << pcbr << "%\n\n";

                if (iters->first != nodes_number-1){
                    myfile << "------------------------------------------------------\n\n";
                }
            }
        }
        
        Simulator::Destroy();
    }
    
    double avg_thr = sum_thr / ((nodes_number-1) + simulations_number);
    
    myfile << "\n-----------------------------------------------------\n";
    myfile << "-------------------final statistics------------------\n";
    myfile << "-----------------------------------------------------\n\n";
    myfile << "--------------avg throughput statistics--------------\n\n";
    myfile << "Total average throughput\t\t" << avg_thr << " kbps\n";
    
    myfile << "\n-------------packet statistics----------------------\n\n";
    myfile << "Total number of CBR packets received\t" << sink_rx_udp * 1. / simulations_number << "\n";
    myfile << "Total number of packets received\t" << sink_rx_pkts * 1. / simulations_number << "\n";
    myfile << "PCBR\t\t\t\t\t" << sink_rx_udp * 1. / sink_rx_pkts * 100. << "%\n\n";
    myfile << "-----------------------------------------------------\n\n";
    
    // close output file
    myfile.close();
    
    return 0;
    
}
